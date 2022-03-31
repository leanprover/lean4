// Lean compiler output
// Module: Lean.Meta.Tactic.Split
// Imports: Init Lean.Meta.Match.MatchEqs Lean.Meta.Tactic.Generalize
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
lean_object* l_List_reverse___rarg(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___spec__1(lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__3;
static lean_object* l_Lean_Meta_Split_simpMatch_pre___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__2;
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__1;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__1;
lean_object* l_Lean_Meta_Simp_simpMatchCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_isMatcherAppCore_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__1;
lean_object* l_Lean_Meta_trySubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__1;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__4;
static lean_object* l_Lean_Meta_Split_simpMatch___closed__2;
static lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__3;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SplitIf_discharge_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__2;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__2;
static lean_object* l_Lean_Meta_Split_simpMatch___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__4;
lean_object* l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(lean_object*);
static lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2___closed__1;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__2;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isIte(lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__7;
lean_object* l_Lean_Meta_Match_MatchEqns_size(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__1;
lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Match_withMkMatcherInput___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1;
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__1;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12;
lean_object* l_Lean_Meta_Cases_unifyEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__10;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkSplitterProof_proveSubgoal___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_throwNestedTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__5;
uint8_t l_Std_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___closed__1;
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__3;
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_splitLocalDecl_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__9;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__4;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarId;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__4;
uint8_t l_Lean_Expr_isDIte(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___closed__3;
static lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6;
lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitIfTarget_x3f___spec__1___at_Lean_Meta_splitIfTarget_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__11;
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f_go(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___closed__4;
static lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___rarg___boxed(lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Split_findSplit_x3f_isCandidate___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__2;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_3263_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___closed__1;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__3;
static lean_object* _init_l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
x_7 = l_Lean_Meta_Simp_neutralConfig;
x_8 = l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1;
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Simp_neutralConfig;
x_15 = l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Split_getSimpMatchContext___rarg___boxed), 2, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Split_getSimpMatchContext___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Split_getSimpMatchContext(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch_pre___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_SplitIf_discharge_x3f___boxed), 9, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_23 = l_Lean_Meta_reduceRecMatcher_x3f(x_1, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
lean_inc(x_1);
x_27 = l_Lean_Meta_Simp_simpMatchCore_x3f(x_22, x_1, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_27, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_41);
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_dec(x_27);
x_43 = lean_ctor_get(x_28, 0);
lean_inc(x_43);
lean_dec(x_28);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
return x_27;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_27, 0);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_27);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_23);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_23, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_24, 0);
lean_inc(x_51);
lean_dec(x_24);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_23, 0, x_54);
return x_23;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_dec(x_23);
x_56 = lean_ctor_get(x_24, 0);
lean_inc(x_56);
lean_dec(x_24);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_23);
if (x_61 == 0)
{
return x_23;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_23, 0);
x_63 = lean_ctor_get(x_23, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_23);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch_pre), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lambda__2___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__1;
x_2 = l_Lean_Meta_Split_simpMatch___closed__2;
x_3 = l_Lean_Meta_Split_simpMatch___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_Split_getSimpMatchContext___rarg(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_Split_simpMatch___closed__4;
x_11 = l_Lean_Meta_Simp_main(x_1, x_8, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Split_simpMatch___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Split_simpMatch___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_3);
x_10 = l_Lean_Meta_instantiateMVars(x_8, x_2, x_3, x_4, x_5, x_9);
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
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatchTarget___lambda__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isAppOf(x_3, x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_16 = l_Lean_Meta_reduceRecMatcher_x3f(x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
lean_inc(x_2);
x_20 = l_Lean_mkConst(x_2, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_2);
x_22 = l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1;
x_23 = lean_unsigned_to_nat(1000u);
x_24 = 1;
x_25 = 0;
x_26 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*5 + 1, x_25);
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 2;
lean_ctor_set_uint8(x_28, 5, x_30);
x_31 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
lean_inc(x_3);
x_32 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_26, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_32, 0, x_38);
return x_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_32, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_32, 0, x_47);
return x_32;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_dec(x_32);
x_49 = lean_ctor_get(x_33, 0);
lean_inc(x_49);
lean_dec(x_33);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
return x_32;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_32, 0);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_32);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_56 = lean_ctor_get_uint8(x_28, 0);
x_57 = lean_ctor_get_uint8(x_28, 1);
x_58 = lean_ctor_get_uint8(x_28, 2);
x_59 = lean_ctor_get_uint8(x_28, 3);
x_60 = lean_ctor_get_uint8(x_28, 4);
x_61 = lean_ctor_get_uint8(x_28, 6);
x_62 = lean_ctor_get_uint8(x_28, 7);
x_63 = lean_ctor_get_uint8(x_28, 8);
x_64 = lean_ctor_get_uint8(x_28, 9);
x_65 = lean_ctor_get_uint8(x_28, 10);
x_66 = lean_ctor_get_uint8(x_28, 11);
x_67 = lean_ctor_get_uint8(x_28, 12);
x_68 = lean_ctor_get_uint8(x_28, 13);
lean_dec(x_28);
x_69 = 2;
x_70 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_70, 0, x_56);
lean_ctor_set_uint8(x_70, 1, x_57);
lean_ctor_set_uint8(x_70, 2, x_58);
lean_ctor_set_uint8(x_70, 3, x_59);
lean_ctor_set_uint8(x_70, 4, x_60);
lean_ctor_set_uint8(x_70, 5, x_69);
lean_ctor_set_uint8(x_70, 6, x_61);
lean_ctor_set_uint8(x_70, 7, x_62);
lean_ctor_set_uint8(x_70, 8, x_63);
lean_ctor_set_uint8(x_70, 9, x_64);
lean_ctor_set_uint8(x_70, 10, x_65);
lean_ctor_set_uint8(x_70, 11, x_66);
lean_ctor_set_uint8(x_70, 12, x_67);
lean_ctor_set_uint8(x_70, 13, x_68);
lean_ctor_set(x_6, 0, x_70);
x_71 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
lean_inc(x_3);
x_72 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_26, x_71, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_3);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_81 = x_72;
} else {
 lean_dec_ref(x_72);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
lean_dec(x_73);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_3);
x_85 = lean_ctor_get(x_72, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_72, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_87 = x_72;
} else {
 lean_dec_ref(x_72);
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
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_89 = lean_ctor_get(x_6, 0);
x_90 = lean_ctor_get(x_6, 1);
x_91 = lean_ctor_get(x_6, 2);
x_92 = lean_ctor_get(x_6, 3);
x_93 = lean_ctor_get(x_6, 4);
x_94 = lean_ctor_get(x_6, 5);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_6);
x_95 = lean_ctor_get_uint8(x_89, 0);
x_96 = lean_ctor_get_uint8(x_89, 1);
x_97 = lean_ctor_get_uint8(x_89, 2);
x_98 = lean_ctor_get_uint8(x_89, 3);
x_99 = lean_ctor_get_uint8(x_89, 4);
x_100 = lean_ctor_get_uint8(x_89, 6);
x_101 = lean_ctor_get_uint8(x_89, 7);
x_102 = lean_ctor_get_uint8(x_89, 8);
x_103 = lean_ctor_get_uint8(x_89, 9);
x_104 = lean_ctor_get_uint8(x_89, 10);
x_105 = lean_ctor_get_uint8(x_89, 11);
x_106 = lean_ctor_get_uint8(x_89, 12);
x_107 = lean_ctor_get_uint8(x_89, 13);
if (lean_is_exclusive(x_89)) {
 x_108 = x_89;
} else {
 lean_dec_ref(x_89);
 x_108 = lean_box(0);
}
x_109 = 2;
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 0, 14);
} else {
 x_110 = x_108;
}
lean_ctor_set_uint8(x_110, 0, x_95);
lean_ctor_set_uint8(x_110, 1, x_96);
lean_ctor_set_uint8(x_110, 2, x_97);
lean_ctor_set_uint8(x_110, 3, x_98);
lean_ctor_set_uint8(x_110, 4, x_99);
lean_ctor_set_uint8(x_110, 5, x_109);
lean_ctor_set_uint8(x_110, 6, x_100);
lean_ctor_set_uint8(x_110, 7, x_101);
lean_ctor_set_uint8(x_110, 8, x_102);
lean_ctor_set_uint8(x_110, 9, x_103);
lean_ctor_set_uint8(x_110, 10, x_104);
lean_ctor_set_uint8(x_110, 11, x_105);
lean_ctor_set_uint8(x_110, 12, x_106);
lean_ctor_set_uint8(x_110, 13, x_107);
x_111 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_90);
lean_ctor_set(x_111, 2, x_91);
lean_ctor_set(x_111, 3, x_92);
lean_ctor_set(x_111, 4, x_93);
lean_ctor_set(x_111, 5, x_94);
x_112 = l_Lean_Meta_Split_simpMatch_pre___closed__1;
lean_inc(x_3);
x_113 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_26, x_112, x_4, x_5, x_111, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_3);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
if (lean_is_scalar(x_116)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_116;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_115);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_3);
x_121 = lean_ctor_get(x_113, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_122 = x_113;
} else {
 lean_dec_ref(x_113);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_114, 0);
lean_inc(x_123);
lean_dec(x_114);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
if (lean_is_scalar(x_122)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_122;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_3);
x_126 = lean_ctor_get(x_113, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_113, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_128 = x_113;
} else {
 lean_dec_ref(x_113);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_16);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_16, 0);
lean_dec(x_131);
x_132 = lean_ctor_get(x_17, 0);
lean_inc(x_132);
lean_dec(x_17);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_16, 0, x_135);
return x_16;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_136 = lean_ctor_get(x_16, 1);
lean_inc(x_136);
lean_dec(x_16);
x_137 = lean_ctor_get(x_17, 0);
lean_inc(x_137);
lean_dec(x_17);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_136);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = !lean_is_exclusive(x_16);
if (x_142 == 0)
{
return x_16;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_16, 0);
x_144 = lean_ctor_get(x_16, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_16);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_Meta_Split_getSimpMatchContext___rarg(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___boxed), 10, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = l_Lean_Meta_Split_simpMatch___closed__2;
x_14 = l_Lean_Meta_Split_simpMatch___closed__3;
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Lean_Meta_Simp_main(x_3, x_10, x_15, x_4, x_5, x_6, x_7, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_Meta_getMVarType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
x_12 = l_Lean_Meta_instantiateMVars(x_10, x_4, x_5, x_6, x_7, x_11);
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
x_20 = l_Lean_Meta_replaceTargetDefEq(x_1, x_19, x_4, x_5, x_6, x_7, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = l_Lean_Meta_replaceTargetEq(x_1, x_23, x_22, x_4, x_5, x_6, x_7, x_21);
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
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
x_10 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Expr_isFVar(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
if (x_7 == 0)
{
lean_object* x_10; 
x_10 = lean_array_push(x_4, x_6);
x_2 = x_9;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_9;
goto _start;
}
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__2;
x_15 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_14, x_6, x_7, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_13, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
x_8 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = l_Lean_Expr_isFVar(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
lean_dec(x_13);
x_18 = l_Lean_instInhabitedFVarId;
x_19 = lean_array_get(x_18, x_1, x_15);
x_20 = lean_array_push(x_16, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_15, x_21);
lean_dec(x_15);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_22);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
x_26 = l_Lean_Expr_fvarId_x21(x_13);
x_27 = lean_array_push(x_16, x_26);
lean_ctor_set(x_5, 1, x_27);
x_28 = 1;
x_29 = lean_usize_add(x_4, x_28);
x_4 = x_29;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_33 = l_Lean_Expr_isFVar(x_13);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
lean_dec(x_13);
x_34 = l_Lean_instInhabitedFVarId;
x_35 = lean_array_get(x_34, x_1, x_31);
x_36 = lean_array_push(x_32, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_31, x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = 1;
x_41 = lean_usize_add(x_4, x_40);
x_4 = x_41;
x_5 = x_39;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
x_43 = l_Lean_Expr_fvarId_x21(x_13);
x_44 = lean_array_push(x_32, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_44);
x_46 = 1;
x_47 = lean_usize_add(x_4, x_46);
x_4 = x_47;
x_5 = x_45;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_array_get_size(x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_box(0);
x_8 = x_21;
goto block_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_box(0);
x_8 = x_23;
goto block_17;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___spec__1(x_2, x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_box(0);
x_8 = x_27;
goto block_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1;
x_29 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1(x_2, x_24, x_25, x_28);
x_30 = lean_array_get_size(x_29);
x_31 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_32 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2(x_31, x_24, x_29, x_3, x_4, x_5, x_6, x_7);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_Lean_Meta_generalize(x_1, x_33, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___closed__1;
x_41 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3(x_39, x_2, x_25, x_24, x_40, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_array_get_size(x_39);
x_47 = l_Array_toSubarray___rarg(x_39, x_44, x_46);
x_48 = l_Array_ofSubarray___rarg(x_47);
lean_ctor_set(x_36, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_36);
lean_ctor_set(x_41, 0, x_49);
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_array_get_size(x_39);
x_55 = l_Array_toSubarray___rarg(x_39, x_52, x_54);
x_56 = l_Array_ofSubarray___rarg(x_55);
lean_ctor_set(x_36, 0, x_56);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_36);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_59 = lean_ctor_get(x_36, 0);
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_36);
x_61 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___closed__1;
x_62 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3(x_59, x_2, x_25, x_24, x_61, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_array_get_size(x_59);
x_69 = l_Array_toSubarray___rarg(x_59, x_66, x_68);
x_70 = l_Array_ofSubarray___rarg(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_60);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_71);
if (lean_is_scalar(x_65)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_65;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_64);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
return x_35;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_35, 0);
x_76 = lean_ctor_get(x_35, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_35);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
block_17:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkSplitterProof_proveSubgoal___spec__1(x_10, x_11, x_2);
x_13 = l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__3(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_trySubst(x_2, x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__2;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("split");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__4;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst auxiliary eq ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_12 = lean_array_uget(x_1, x_3);
x_20 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__6;
x_51 = lean_st_ref_get(x_8, x_9);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = 0;
x_21 = x_56;
x_22 = x_55;
goto block_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_20, x_5, x_6, x_7, x_8, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unbox(x_59);
lean_dec(x_59);
x_21 = x_61;
x_22 = x_60;
goto block_50;
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_15;
x_9 = x_14;
goto _start;
}
block_50:
{
if (x_21 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___lambda__1(x_12, x_4, x_23, x_5, x_6, x_7, x_8, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_13 = x_25;
x_14 = x_26;
goto block_19;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_inc(x_12);
x_27 = l_Lean_mkFVar(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_27);
x_28 = lean_infer_type(x_27, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_27);
x_32 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__8;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__10;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_29);
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_20, x_39, x_5, x_6, x_7, x_8, x_30);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___lambda__1(x_12, x_4, x_41, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_13 = x_44;
x_14 = x_45;
goto block_19;
}
else
{
uint8_t x_46; 
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_28);
if (x_46 == 0)
{
return x_28;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_28, 0);
x_48 = lean_ctor_get(x_28, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_28);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = l_Array_reverse___rarg(x_2);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1(x_8, x_10, x_11, x_1, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Meta_Cases_unifyEqs(x_1, x_2, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_dec(x_30);
x_31 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(x_29, x_5, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_3, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_4);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_35);
lean_ctor_set(x_31, 0, x_26);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_3, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_4);
lean_ctor_set(x_26, 1, x_41);
lean_ctor_set(x_26, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_26);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_26, 0);
lean_inc(x_47);
lean_dec(x_26);
x_48 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(x_47, x_5, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
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
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_3, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
if (lean_is_scalar(x_51)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_51;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_4);
x_57 = lean_ctor_get(x_48, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_59 = x_48;
} else {
 lean_dec_ref(x_48);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_14);
if (x_61 == 0)
{
return x_14;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("before unifyEqs\n");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_ctor_get(x_1, 2);
x_19 = l_instInhabitedNat;
x_20 = lean_array_get(x_19, x_18, x_16);
x_21 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_22 = l_Lean_Meta_introNCore(x_14, x_20, x_5, x_21, x_21, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_54 = lean_st_ref_get(x_11, x_24);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 3);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get_uint8(x_56, sizeof(void*)*1);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_26 = x_21;
x_27 = x_58;
goto block_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
lean_inc(x_2);
x_60 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_2, x_8, x_9, x_10, x_11, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unbox(x_61);
lean_dec(x_61);
x_26 = x_63;
x_27 = x_62;
goto block_53;
}
block_53:
{
if (x_26 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_4);
x_29 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_4, x_25, x_16, x_17, x_3, x_28, x_8, x_9, x_10, x_11, x_27);
lean_dec(x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_6 = x_30;
x_7 = x_15;
x_12 = x_31;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_25);
x_37 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_37, 0, x_25);
x_38 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_2);
x_42 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_41, x_8, x_9, x_10, x_11, x_27);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_4);
x_45 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_4, x_25, x_16, x_17, x_3, x_43, x_8, x_9, x_10, x_11, x_44);
lean_dec(x_43);
lean_dec(x_16);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_6 = x_46;
x_7 = x_15;
x_12 = x_47;
goto _start;
}
else
{
uint8_t x_49; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 0);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_45);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_22);
if (x_64 == 0)
{
return x_22;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_22, 0);
x_66 = lean_ctor_get(x_22, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_22);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2(x_2, x_3, x_4, x_5, x_1, x_14, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_List_reverse___rarg(x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_reverse___rarg(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
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
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'applyMatchSplitter' failed, unexpected number of goals created after applying splitter for '");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'.");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_getMVarType(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
x_19 = 1;
x_20 = 1;
lean_inc(x_2);
x_21 = l_Lean_Meta_mkLambdaFVars(x_2, x_16, x_18, x_19, x_20, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_mkApp(x_3, x_22);
x_25 = l_Lean_mkAppN(x_24, x_2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_25);
x_26 = l_Lean_Meta_check(x_25, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_29 = l_Lean_Meta_apply(x_1, x_25, x_28, x_10, x_11, x_12, x_13, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_List_lengthTRAux___rarg(x_30, x_32);
x_34 = l_Lean_Meta_Match_MatchEqns_size(x_5);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_36, 0, x_9);
x_37 = l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__2;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__4;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_40, x_10, x_11, x_12, x_13, x_31);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_9);
x_46 = lean_box(0);
x_47 = l_Lean_Meta_Split_applyMatchSplitter___lambda__1(x_4, x_5, x_6, x_7, x_8, x_30, x_46, x_10, x_11, x_12, x_13, x_31);
lean_dec(x_5);
return x_47;
}
}
else
{
uint8_t x_48; 
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
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
return x_29;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_25);
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
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_26);
if (x_52 == 0)
{
return x_26;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_26, 0);
x_54 = lean_ctor_get(x_26, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_26);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_21);
if (x_56 == 0)
{
return x_21;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_21, 0);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_21);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
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
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
return x_15;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_get_size(x_1);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_18, x_2, x_1);
lean_inc(x_3);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lambda__2), 14, 9);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_4);
lean_closure_set(x_20, 3, x_5);
lean_closure_set(x_20, 4, x_6);
lean_closure_set(x_20, 5, x_7);
lean_closure_set(x_20, 6, x_8);
lean_closure_set(x_20, 7, x_9);
lean_closure_set(x_20, 8, x_10);
x_21 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_3, x_20, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after introN\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_9);
x_15 = lean_array_get_size(x_1);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_15);
x_18 = l_Lean_Meta_introNCore(x_2, x_15, x_16, x_17, x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
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
x_37 = lean_st_ref_get(x_13, x_20);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_23 = x_17;
x_24 = x_41;
goto block_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
lean_inc(x_6);
x_43 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_6, x_10, x_11, x_12, x_13, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_23 = x_46;
x_24 = x_45;
goto block_36;
}
block_36:
{
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3(x_21, x_3, x_22, x_4, x_16, x_5, x_6, x_7, x_15, x_8, x_25, x_10, x_11, x_12, x_13, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_22);
x_27 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_28 = l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_6);
x_32 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_6, x_31, x_10, x_11, x_12, x_13, x_24);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3(x_21, x_3, x_22, x_4, x_16, x_5, x_6, x_7, x_15, x_8, x_33, x_10, x_11, x_12, x_13, x_34);
lean_dec(x_33);
return x_35;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_18);
if (x_47 == 0)
{
return x_18;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after generalize\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_16 = lean_array_get_size(x_1);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_17, x_18, x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = l_Lean_Meta_generalizeTargetsEq(x_2, x_3, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_37 = lean_st_ref_get(x_14, x_22);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = 0;
x_23 = x_42;
x_24 = x_41;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
lean_inc(x_7);
x_44 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_7, x_11, x_12, x_13, x_14, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unbox(x_45);
lean_dec(x_45);
x_23 = x_47;
x_24 = x_46;
goto block_36;
}
block_36:
{
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Meta_Split_applyMatchSplitter___lambda__4(x_4, x_21, x_18, x_5, x_6, x_7, x_8, x_9, x_25, x_11, x_12, x_13, x_14, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_21);
x_27 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_27, 0, x_21);
x_28 = l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_7);
x_32 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_7, x_31, x_11, x_12, x_13, x_14, x_24);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Split_applyMatchSplitter___lambda__4(x_4, x_21, x_18, x_5, x_6, x_7, x_8, x_9, x_33, x_11, x_12, x_13, x_14, x_34);
return x_35;
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_20);
if (x_48 == 0)
{
return x_20;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after generalizeMatchDiscrs\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(x_1, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_35 = lean_st_ref_get(x_12, x_17);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = 0;
x_21 = x_40;
x_22 = x_39;
goto block_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
lean_inc(x_6);
x_42 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_6, x_9, x_10, x_11, x_12, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_unbox(x_43);
lean_dec(x_43);
x_21 = x_45;
x_22 = x_44;
goto block_34;
}
block_34:
{
if (x_21 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Meta_Split_applyMatchSplitter___lambda__5(x_18, x_20, x_3, x_2, x_4, x_5, x_6, x_19, x_7, x_23, x_9, x_10, x_11, x_12, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_20);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_26 = l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__2;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_6);
x_30 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_6, x_29, x_9, x_10, x_11, x_12, x_22);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_Split_applyMatchSplitter___lambda__5(x_18, x_20, x_3, x_2, x_4, x_5, x_6, x_19, x_7, x_31, x_9, x_10, x_11, x_12, x_32);
return x_33;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
return x_14;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("applyMatchSplitter\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_to_list(lean_box(0), x_6);
x_15 = l_Lean_mkConst(x_13, x_14);
x_16 = l_Lean_mkAppN(x_15, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_16);
x_17 = lean_infer_type(x_16, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Meta_whnfForall(x_18, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_bindingDomain_x21(x_21);
lean_dec(x_21);
x_24 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__6;
x_39 = lean_st_ref_get(x_11, x_22);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = 0;
x_25 = x_44;
x_26 = x_43;
goto block_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_24, x_8, x_9, x_10, x_11, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_25 = x_49;
x_26 = x_48;
goto block_38;
}
block_38:
{
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l_Lean_Meta_Split_applyMatchSplitter___lambda__6(x_3, x_4, x_23, x_16, x_1, x_24, x_5, x_27, x_8, x_9, x_10, x_11, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_3);
x_29 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_29, 0, x_3);
x_30 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_24, x_33, x_8, x_9, x_10, x_11, x_26);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_Split_applyMatchSplitter___lambda__6(x_3, x_4, x_23, x_16, x_1, x_24, x_5, x_35, x_8, x_9, x_10, x_11, x_36);
return x_37;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_20);
if (x_50 == 0)
{
return x_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_20, 0);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_20);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_17);
if (x_54 == 0)
{
return x_17;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_17, 0);
x_56 = lean_ctor_get(x_17, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_17);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'applyMatchSplitter' failed, '");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a 'match' auxiliary declaration.");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_11 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = l_Lean_Meta_Split_applyMatchSplitter___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_Split_applyMatchSplitter___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(x_18, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_22 = lean_get_match_equations_for(x_2, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 3);
lean_inc(x_23);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7(x_24, x_4, x_1, x_5, x_2, x_3, x_26, x_6, x_7, x_8, x_9, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = l_Lean_levelZero;
x_32 = lean_array_set(x_3, x_30, x_31);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = l_Lean_Meta_Split_applyMatchSplitter___lambda__7(x_28, x_4, x_1, x_5, x_2, x_32, x_33, x_6, x_7, x_8, x_9, x_29);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Split_applyMatchSplitter___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; lean_object* x_18; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = l_Lean_Meta_Split_applyMatchSplitter___lambda__3(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Lean_Meta_Split_applyMatchSplitter___lambda__4(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_2, 0);
x_18 = l_Lean_instInhabitedName;
x_19 = lean_array_get(x_18, x_17, x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_20 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_13, x_1, x_19, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_15, x_23);
lean_dec(x_15);
lean_ctor_set(x_4, 1, x_16);
lean_ctor_set(x_4, 0, x_21);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_24);
x_4 = x_14;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_free_object(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
x_34 = lean_ctor_get(x_2, 0);
x_35 = l_Lean_instInhabitedName;
x_36 = lean_array_get(x_35, x_34, x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_37 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_30, x_1, x_36, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_32, x_40);
lean_dec(x_32);
lean_ctor_set(x_4, 1, x_33);
lean_ctor_set(x_4, 0, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
x_3 = x_42;
x_4 = x_31;
x_9 = x_39;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_4);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_46 = x_37;
} else {
 lean_dec_ref(x_37);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
x_50 = lean_ctor_get(x_3, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_52 = x_3;
} else {
 lean_dec_ref(x_3);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_2, 0);
x_54 = l_Lean_instInhabitedName;
x_55 = lean_array_get(x_54, x_53, x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_56 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_48, x_1, x_55, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_50, x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_51);
if (lean_is_scalar(x_52)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_52;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_3 = x_62;
x_4 = x_49;
x_9 = x_58;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_66 = x_56;
} else {
 lean_dec_ref(x_56);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("splitMatch");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Split_splitMatch___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match application expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_splitMatch___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___closed__5() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Meta_Match_withMkMatcherInput___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_Split_splitMatch___closed__4;
x_21 = l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(x_20, x_3, x_4, x_5, x_6, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_8 = x_22;
x_9 = x_23;
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_27 = lean_get_match_equations_for(x_26, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 5);
lean_inc(x_32);
lean_dec(x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_33 = l_Lean_Meta_Split_applyMatchSplitter(x_1, x_26, x_30, x_31, x_32, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_Split_splitMatch___closed__5;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1(x_26, x_28, x_36, x_34, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_28);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_List_reverse___rarg(x_40);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_List_reverse___rarg(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_dec(x_37);
x_8 = x_47;
x_9 = x_48;
goto block_16;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_28);
lean_dec(x_26);
x_49 = lean_ctor_get(x_33, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_dec(x_33);
x_8 = x_49;
x_9 = x_50;
goto block_16;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_1);
x_51 = lean_ctor_get(x_27, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_27, 1);
lean_inc(x_52);
lean_dec(x_27);
x_8 = x_51;
x_9 = x_52;
goto block_16;
}
}
block_16:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Split_splitMatch___closed__2;
x_11 = l_Lean_Meta_throwNestedTacticEx___rarg(x_10, x_8, x_3, x_4, x_5, x_6, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_foldlM___at_Lean_Meta_Split_splitMatch___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__1() {
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
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_array_get(x_13, x_1, x_4);
x_15 = l_Lean_Expr_hasLooseBVars(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
{
lean_object* _tmp_2 = x_12;
lean_object* _tmp_3 = x_16;
lean_object* _tmp_6 = x_2;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_4);
x_18 = l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__2;
return x_18;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_7);
return x_7;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_7);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Split_findSplit_x3f_isCandidate___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__2() {
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
static lean_object* _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_findSplit_x3f_isCandidate___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__3;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__5;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_26; 
lean_inc(x_4);
x_26 = l_Std_HashSetImp_contains___at_Lean_CollectMVars_visit___spec__1(x_3, x_4);
if (x_26 == 0)
{
if (x_2 == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
x_5 = x_27;
goto block_25;
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Expr_isIte(x_4);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Expr_isDIte(x_4);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_5 = x_30;
goto block_25;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_1);
x_31 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6;
x_32 = l_Lean_Expr_getRevArg_x21(x_4, x_31);
x_33 = l_Lean_Expr_hasLooseBVars(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; 
x_34 = 1;
x_35 = lean_box(x_34);
return x_35;
}
else
{
uint8_t x_36; lean_object* x_37; 
x_36 = 0;
x_37 = lean_box(x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_1);
x_38 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6;
x_39 = l_Lean_Expr_getRevArg_x21(x_4, x_38);
x_40 = l_Lean_Expr_hasLooseBVars(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; 
x_41 = 1;
x_42 = lean_box(x_41);
return x_42;
}
else
{
uint8_t x_43; lean_object* x_44; 
x_43 = 0;
x_44 = lean_box(x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; lean_object* x_46; 
lean_dec(x_4);
lean_dec(x_1);
x_45 = 0;
x_46 = lean_box(x_45);
return x_46;
}
block_25:
{
lean_object* x_6; 
lean_dec(x_5);
x_6 = l_Lean_Meta_isMatcherAppCore_x3f(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = 0;
x_8 = lean_box(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Expr_getAppNumArgsAux(x_4, x_10);
x_12 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_4, x_13, x_15);
x_17 = l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(x_9);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_18);
x_20 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__2;
lean_inc(x_19);
x_21 = l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1(x_16, x_20, x_19, x_17, x_19, x_14, x_20);
lean_dec(x_19);
lean_dec(x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__4;
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f_isCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Split_findSplit_x3f_isCandidate(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Split_findSplit_x3f_isCandidate___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_3);
lean_inc(x_4);
x_7 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_6, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_Expr_isIte(x_4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isDIte(x_4);
lean_dec(x_4);
if (x_12 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6;
lean_inc(x_10);
x_14 = l_Lean_Expr_getRevArg_x21(x_10, x_13);
x_15 = l_Lean_Meta_Split_findSplit_x3f_go(x_1, x_2, x_3, x_14);
if (lean_obj_tag(x_15) == 0)
{
return x_7;
}
else
{
uint8_t x_16; 
lean_free_object(x_7);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_19 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6;
lean_inc(x_10);
x_20 = l_Lean_Expr_getRevArg_x21(x_10, x_19);
x_21 = l_Lean_Meta_Split_findSplit_x3f_go(x_1, x_2, x_3, x_20);
if (lean_obj_tag(x_21) == 0)
{
return x_7;
}
else
{
uint8_t x_22; 
lean_free_object(x_7);
lean_dec(x_10);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = l_Lean_Expr_isIte(x_4);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_isDIte(x_4);
lean_dec(x_4);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6;
lean_inc(x_25);
x_30 = l_Lean_Expr_getRevArg_x21(x_25, x_29);
x_31 = l_Lean_Meta_Split_findSplit_x3f_go(x_1, x_2, x_3, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_25);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
x_36 = l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6;
lean_inc(x_25);
x_37 = l_Lean_Expr_getRevArg_x21(x_25, x_36);
x_38 = l_Lean_Meta_Split_findSplit_x3f_go(x_1, x_2, x_3, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_25);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_25);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Split_findSplit_x3f_go(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Split_findSplit_x3f_go(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_findSplit_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Meta_Split_findSplit_x3f(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_splitTarget_x3f_go___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find term to split\n");
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
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_4);
x_14 = l_Lean_Meta_Split_findSplit_x3f_go(x_13, x_2, x_4, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__6;
x_31 = lean_st_ref_get(x_8, x_12);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = 0;
x_16 = x_36;
x_17 = x_35;
goto block_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_15, x_5, x_6, x_7, x_8, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
x_16 = x_41;
x_17 = x_40;
goto block_30;
}
block_30:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_splitTarget_x3f_go___closed__1;
if (x_16 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_apply_6(x_18, x_19, x_5, x_6, x_7, x_8, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = l_Lean_Meta_splitTarget_x3f_go___closed__3;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_15, x_25, x_5, x_6, x_7, x_8, x_17);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_apply_6(x_18, x_27, x_5, x_6, x_7, x_8, x_28);
return x_29;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = l_Lean_Expr_isIte(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Expr_isDIte(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_43);
lean_inc(x_1);
x_46 = l_Lean_Meta_Split_splitMatch(x_1, x_43, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_ctor_set(x_14, 0, x_48);
lean_ctor_set(x_46, 0, x_14);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_14, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_14);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_14);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = l_Std_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_4, x_43);
x_4 = x_53;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_free_object(x_14);
lean_dec(x_43);
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_box(0);
x_56 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitIfTarget_x3f___spec__1___at_Lean_Meta_splitIfTarget_x3f___spec__2(x_1, x_55, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
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
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_56, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_57, 0, x_72);
return x_56;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_56, 1);
lean_inc(x_73);
lean_dec(x_56);
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec(x_64);
x_75 = lean_ctor_get(x_65, 0);
lean_inc(x_75);
lean_dec(x_65);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_57, 0, x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_57);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_80 = lean_ctor_get(x_57, 0);
lean_inc(x_80);
lean_dec(x_57);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_56, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_84 = x_56;
} else {
 lean_dec_ref(x_56);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
if (lean_is_scalar(x_84)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_84;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
return x_91;
}
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_56);
if (x_92 == 0)
{
return x_56;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_56, 0);
x_94 = lean_ctor_get(x_56, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_56);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_free_object(x_14);
lean_dec(x_43);
lean_dec(x_4);
lean_dec(x_3);
x_96 = lean_box(0);
x_97 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitIfTarget_x3f___spec__1___at_Lean_Meta_splitIfTarget_x3f___spec__2(x_1, x_96, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_97, 0);
lean_dec(x_100);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_98);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_98, 0);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = !lean_is_exclusive(x_97);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_97, 0);
lean_dec(x_108);
x_109 = lean_ctor_get(x_105, 0);
lean_inc(x_109);
lean_dec(x_105);
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_98, 0, x_113);
return x_97;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_97, 1);
lean_inc(x_114);
lean_dec(x_97);
x_115 = lean_ctor_get(x_105, 0);
lean_inc(x_115);
lean_dec(x_105);
x_116 = lean_ctor_get(x_106, 0);
lean_inc(x_116);
lean_dec(x_106);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_98, 0, x_119);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_98);
lean_ctor_set(x_120, 1, x_114);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_121 = lean_ctor_get(x_98, 0);
lean_inc(x_121);
lean_dec(x_98);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_97, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_125 = x_97;
} else {
 lean_dec_ref(x_97);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_122, 0);
lean_inc(x_126);
lean_dec(x_122);
x_127 = lean_ctor_get(x_123, 0);
lean_inc(x_127);
lean_dec(x_123);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
if (lean_is_scalar(x_125)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_125;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_124);
return x_132;
}
}
}
else
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_97);
if (x_133 == 0)
{
return x_97;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_97, 0);
x_135 = lean_ctor_get(x_97, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_97);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
else
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_14, 0);
lean_inc(x_137);
lean_dec(x_14);
x_138 = l_Lean_Expr_isIte(x_137);
if (x_138 == 0)
{
uint8_t x_139; 
x_139 = l_Lean_Expr_isDIte(x_137);
if (x_139 == 0)
{
lean_object* x_140; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_137);
lean_inc(x_1);
x_140 = l_Lean_Meta_Split_splitMatch(x_1, x_137, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_137);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_141);
if (lean_is_scalar(x_143)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_143;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_dec(x_140);
x_147 = l_Std_HashSetImp_insert___at_Lean_CollectMVars_visit___spec__3(x_4, x_137);
x_4 = x_147;
x_9 = x_146;
goto _start;
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_137);
lean_dec(x_4);
lean_dec(x_3);
x_149 = lean_box(0);
x_150 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitIfTarget_x3f___spec__1___at_Lean_Meta_splitIfTarget_x3f___spec__2(x_1, x_149, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_156 = x_151;
} else {
 lean_dec_ref(x_151);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
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
x_161 = lean_ctor_get(x_157, 0);
lean_inc(x_161);
lean_dec(x_157);
x_162 = lean_ctor_get(x_158, 0);
lean_inc(x_162);
lean_dec(x_158);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_161);
lean_ctor_set(x_165, 1, x_164);
if (lean_is_scalar(x_156)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_156;
}
lean_ctor_set(x_166, 0, x_165);
if (lean_is_scalar(x_160)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_160;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_159);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_150, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_150, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_170 = x_150;
} else {
 lean_dec_ref(x_150);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_137);
lean_dec(x_4);
lean_dec(x_3);
x_172 = lean_box(0);
x_173 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitIfTarget_x3f___spec__1___at_Lean_Meta_splitIfTarget_x3f___spec__2(x_1, x_172, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_172);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_178 = lean_ctor_get(x_174, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_179 = x_174;
} else {
 lean_dec_ref(x_174);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_182 = lean_ctor_get(x_173, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_183 = x_173;
} else {
 lean_dec_ref(x_173);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
lean_dec(x_180);
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
lean_dec(x_181);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_187);
if (lean_is_scalar(x_179)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_179;
}
lean_ctor_set(x_189, 0, x_188);
if (lean_is_scalar(x_183)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_183;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_182);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_173, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_173, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_193 = x_173;
} else {
 lean_dec_ref(x_173);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_splitTarget_x3f_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_10, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_27 = x_11;
} else {
 lean_dec_ref(x_11);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_dec(x_10);
x_32 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_saveState___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Meta_getMVarType(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_4);
x_14 = l_Lean_Meta_instantiateMVars(x_12, x_3, x_4, x_5, x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Meta_splitTarget_x3f_go(x_1, x_2, x_15, x_17, x_3, x_4, x_5, x_6, x_16);
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
x_21 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
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
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_18, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_18, 0, x_32);
return x_18;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_35 = x_19;
} else {
 lean_dec_ref(x_19);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_dec(x_18);
x_40 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_1);
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_dec(x_11);
x_47 = l_Lean_Meta_SavedState_restore(x_9, x_3, x_4, x_5, x_6, x_46);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_9);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_splitLocalDecl_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_box(0);
x_14 = 0;
x_15 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_Meta_introNCore(x_11, x_1, x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_List_mapM___at_Lean_Meta_splitLocalDecl_x3f___spec__1(x_1, x_12, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_2, 1, x_22);
lean_ctor_set(x_2, 0, x_19);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_19);
lean_free_object(x_2);
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
uint8_t x_30; 
lean_free_object(x_2);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = 0;
x_38 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_39 = l_Lean_Meta_introNCore(x_34, x_1, x_36, x_37, x_38, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_List_mapM___at_Lean_Meta_splitLocalDecl_x3f___spec__1(x_1, x_35, x_3, x_4, x_5, x_6, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_42);
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_51 = x_43;
} else {
 lean_dec_ref(x_43);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = lean_ctor_get(x_39, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_55 = x_39;
} else {
 lean_dec_ref(x_39);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_splitLocalDecl_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = l_Lean_mkFVar(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = lean_infer_type(x_12, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_4);
x_16 = l_Lean_Meta_instantiateMVars(x_14, x_3, x_4, x_5, x_6, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = 1;
x_21 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2___closed__1;
x_22 = l_Lean_Meta_Split_findSplit_x3f_go(x_11, x_20, x_21, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
uint8_t x_24; 
lean_free_object(x_16);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = l_Lean_Expr_isIte(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_isDIte(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_28 = l_Lean_Meta_splitLocalDecl_x3f___lambda__1___closed__1;
x_29 = lean_array_push(x_28, x_1);
x_30 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Meta_revert(x_2, x_29, x_30, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_array_get_size(x_34);
lean_dec(x_34);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = l_Lean_Meta_Split_splitMatch(x_35, x_25, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_List_mapM___at_Lean_Meta_splitLocalDecl_x3f___spec__1(x_36, x_38, x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_ctor_set(x_22, 0, x_42);
lean_ctor_set(x_40, 0, x_22);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_40);
lean_ctor_set(x_22, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_22);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_free_object(x_22);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
return x_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
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
lean_dec(x_36);
lean_free_object(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_free_object(x_22);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_31);
if (x_54 == 0)
{
return x_31;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_31, 0);
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_31);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_free_object(x_22);
lean_dec(x_25);
x_58 = lean_box(0);
x_59 = l_Lean_Meta_splitIfLocalDecl_x3f(x_2, x_1, x_58, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_59, 0);
lean_dec(x_62);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_59, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_60, 0, x_73);
return x_59;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_59, 1);
lean_inc(x_75);
lean_dec(x_59);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_60, 0, x_80);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_60);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_82 = lean_ctor_get(x_60, 0);
lean_inc(x_82);
lean_dec(x_60);
x_83 = lean_ctor_get(x_59, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_84 = x_59;
} else {
 lean_dec_ref(x_59);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
if (lean_is_scalar(x_84)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_84;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
return x_91;
}
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_59);
if (x_92 == 0)
{
return x_59;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_59, 0);
x_94 = lean_ctor_get(x_59, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_59);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_free_object(x_22);
lean_dec(x_25);
x_96 = lean_box(0);
x_97 = l_Lean_Meta_splitIfLocalDecl_x3f(x_2, x_1, x_96, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_97, 0);
lean_dec(x_100);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_96);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_98);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_97);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_98, 0);
x_106 = lean_ctor_get(x_97, 0);
lean_dec(x_106);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_107);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_98, 0, x_111);
return x_97;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_98, 0);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
lean_dec(x_97);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_98, 0, x_118);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_98);
lean_ctor_set(x_119, 1, x_113);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_120 = lean_ctor_get(x_98, 0);
lean_inc(x_120);
lean_dec(x_98);
x_121 = lean_ctor_get(x_97, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_122 = x_97;
} else {
 lean_dec_ref(x_97);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
if (lean_is_scalar(x_122)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_122;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_121);
return x_129;
}
}
}
else
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_97);
if (x_130 == 0)
{
return x_97;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_97, 0);
x_132 = lean_ctor_get(x_97, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_97);
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
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_22, 0);
lean_inc(x_134);
lean_dec(x_22);
x_135 = l_Lean_Expr_isIte(x_134);
if (x_135 == 0)
{
uint8_t x_136; 
x_136 = l_Lean_Expr_isDIte(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_137 = l_Lean_Meta_splitLocalDecl_x3f___lambda__1___closed__1;
x_138 = lean_array_push(x_137, x_1);
x_139 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_140 = l_Lean_Meta_revert(x_2, x_138, x_139, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_array_get_size(x_143);
lean_dec(x_143);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_146 = l_Lean_Meta_Split_splitMatch(x_144, x_134, x_3, x_4, x_5, x_6, x_142);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_List_mapM___at_Lean_Meta_splitLocalDecl_x3f___spec__1(x_145, x_147, x_3, x_4, x_5, x_6, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_150);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_149, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_149, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_157 = x_149;
} else {
 lean_dec_ref(x_149);
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
lean_dec(x_145);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_159 = lean_ctor_get(x_146, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_146, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_161 = x_146;
} else {
 lean_dec_ref(x_146);
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
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_134);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_163 = lean_ctor_get(x_140, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_140, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_165 = x_140;
} else {
 lean_dec_ref(x_140);
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
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_134);
x_167 = lean_box(0);
x_168 = l_Lean_Meta_splitIfLocalDecl_x3f(x_2, x_1, x_167, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_167);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_173 = lean_ctor_get(x_169, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_174 = x_169;
} else {
 lean_dec_ref(x_169);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_168, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_176 = x_168;
} else {
 lean_dec_ref(x_168);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
lean_dec(x_173);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_180);
if (lean_is_scalar(x_174)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_174;
}
lean_ctor_set(x_182, 0, x_181);
if (lean_is_scalar(x_176)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_176;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_175);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_168, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_168, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_186 = x_168;
} else {
 lean_dec_ref(x_168);
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
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_134);
x_188 = lean_box(0);
x_189 = l_Lean_Meta_splitIfLocalDecl_x3f(x_2, x_1, x_188, x_3, x_4, x_5, x_6, x_19);
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
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_194 = lean_ctor_get(x_190, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_195 = x_190;
} else {
 lean_dec_ref(x_190);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_189, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_197 = x_189;
} else {
 lean_dec_ref(x_189);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_194, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_dec(x_194);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_198);
lean_ctor_set(x_202, 1, x_201);
if (lean_is_scalar(x_195)) {
 x_203 = lean_alloc_ctor(1, 1, 0);
} else {
 x_203 = x_195;
}
lean_ctor_set(x_203, 0, x_202);
if (lean_is_scalar(x_197)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_197;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_196);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_189, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_189, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_207 = x_189;
} else {
 lean_dec_ref(x_189);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_16, 0);
x_210 = lean_ctor_get(x_16, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_16);
x_211 = 1;
x_212 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2___closed__1;
x_213 = l_Lean_Meta_Split_findSplit_x3f_go(x_11, x_211, x_212, x_209);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_214 = lean_box(0);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_210);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_216 = lean_ctor_get(x_213, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_217 = x_213;
} else {
 lean_dec_ref(x_213);
 x_217 = lean_box(0);
}
x_218 = l_Lean_Expr_isIte(x_216);
if (x_218 == 0)
{
uint8_t x_219; 
x_219 = l_Lean_Expr_isDIte(x_216);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; 
x_220 = l_Lean_Meta_splitLocalDecl_x3f___lambda__1___closed__1;
x_221 = lean_array_push(x_220, x_1);
x_222 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_223 = l_Lean_Meta_revert(x_2, x_221, x_222, x_3, x_4, x_5, x_6, x_210);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
x_228 = lean_array_get_size(x_226);
lean_dec(x_226);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_229 = l_Lean_Meta_Split_splitMatch(x_227, x_216, x_3, x_4, x_5, x_6, x_225);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = l_List_mapM___at_Lean_Meta_splitLocalDecl_x3f___spec__1(x_228, x_230, x_3, x_4, x_5, x_6, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_236 = x_217;
}
lean_ctor_set(x_236, 0, x_233);
if (lean_is_scalar(x_235)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_235;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_234);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_217);
x_238 = lean_ctor_get(x_232, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_232, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_240 = x_232;
} else {
 lean_dec_ref(x_232);
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
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_228);
lean_dec(x_217);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_242 = lean_ctor_get(x_229, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_229, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_244 = x_229;
} else {
 lean_dec_ref(x_229);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_246 = lean_ctor_get(x_223, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_223, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_248 = x_223;
} else {
 lean_dec_ref(x_223);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_217);
lean_dec(x_216);
x_250 = lean_box(0);
x_251 = l_Lean_Meta_splitIfLocalDecl_x3f(x_2, x_1, x_250, x_3, x_4, x_5, x_6, x_210);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_250);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_256 = lean_ctor_get(x_252, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 x_257 = x_252;
} else {
 lean_dec_ref(x_252);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_251, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_259 = x_251;
} else {
 lean_dec_ref(x_251);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_256, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_256, 1);
lean_inc(x_261);
lean_dec(x_256);
x_262 = lean_box(0);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_260);
lean_ctor_set(x_264, 1, x_263);
if (lean_is_scalar(x_257)) {
 x_265 = lean_alloc_ctor(1, 1, 0);
} else {
 x_265 = x_257;
}
lean_ctor_set(x_265, 0, x_264);
if (lean_is_scalar(x_259)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_259;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_258);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_251, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_251, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_269 = x_251;
} else {
 lean_dec_ref(x_251);
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
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_217);
lean_dec(x_216);
x_271 = lean_box(0);
x_272 = l_Lean_Meta_splitIfLocalDecl_x3f(x_2, x_1, x_271, x_3, x_4, x_5, x_6, x_210);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_271);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_277 = lean_ctor_get(x_273, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_278 = x_273;
} else {
 lean_dec_ref(x_273);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_272, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_280 = x_272;
} else {
 lean_dec_ref(x_272);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_277, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_277, 1);
lean_inc(x_282);
lean_dec(x_277);
x_283 = lean_box(0);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_284);
if (lean_is_scalar(x_278)) {
 x_286 = lean_alloc_ctor(1, 1, 0);
} else {
 x_286 = x_278;
}
lean_ctor_set(x_286, 0, x_285);
if (lean_is_scalar(x_280)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_280;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_279);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_272, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_272, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_290 = x_272;
} else {
 lean_dec_ref(x_272);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_292 = !lean_is_exclusive(x_13);
if (x_292 == 0)
{
return x_13;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_13, 0);
x_294 = lean_ctor_get(x_13, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_13);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_splitLocalDecl_x3f___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_3263_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__6;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchEqs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Generalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1 = _init_l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_getSimpMatchContext___rarg___closed__1);
l_Lean_Meta_Split_simpMatch_pre___closed__1 = _init_l_Lean_Meta_Split_simpMatch_pre___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch_pre___closed__1);
l_Lean_Meta_Split_simpMatch___closed__1 = _init_l_Lean_Meta_Split_simpMatch___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__1);
l_Lean_Meta_Split_simpMatch___closed__2 = _init_l_Lean_Meta_Split_simpMatch___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__2);
l_Lean_Meta_Split_simpMatch___closed__3 = _init_l_Lean_Meta_Split_simpMatch___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__3);
l_Lean_Meta_Split_simpMatch___closed__4 = _init_l_Lean_Meta_Split_simpMatch___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__4);
l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___spec__2___closed__2);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__5 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__5);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__6 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__6);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__7 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__7);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__8 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__8);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__9 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__9);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__10 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__10);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__11 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__11);
l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___spec__1___closed__12);
l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1 = _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__1);
l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2 = _init_l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2();
lean_mark_persistent(l_List_foldlM___at_Lean_Meta_Split_applyMatchSplitter___spec__2___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__3 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__3);
l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__4 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__2___closed__4);
l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__4___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__5___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__6___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lambda__7___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___closed__3 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__3);
l_Lean_Meta_Split_applyMatchSplitter___closed__4 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__4);
l_Lean_Meta_Split_splitMatch___closed__1 = _init_l_Lean_Meta_Split_splitMatch___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___closed__1);
l_Lean_Meta_Split_splitMatch___closed__2 = _init_l_Lean_Meta_Split_splitMatch___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___closed__2);
l_Lean_Meta_Split_splitMatch___closed__3 = _init_l_Lean_Meta_Split_splitMatch___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___closed__3);
l_Lean_Meta_Split_splitMatch___closed__4 = _init_l_Lean_Meta_Split_splitMatch___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___closed__4);
l_Lean_Meta_Split_splitMatch___closed__5 = _init_l_Lean_Meta_Split_splitMatch___closed__5();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___closed__5);
l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_Split_findSplit_x3f_isCandidate___spec__1___closed__2);
l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__1 = _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__1);
l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__2 = _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__2);
l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__3 = _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__3);
l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__4 = _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__4);
l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__5 = _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__5();
lean_mark_persistent(l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__5);
l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6 = _init_l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6();
lean_mark_persistent(l_Lean_Meta_Split_findSplit_x3f_isCandidate___closed__6);
l_Lean_Meta_splitTarget_x3f_go___closed__1 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__1();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__1);
l_Lean_Meta_splitTarget_x3f_go___closed__2 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__2();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__2);
l_Lean_Meta_splitTarget_x3f_go___closed__3 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__3();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__3);
l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2___closed__1 = _init_l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2___closed__1();
lean_mark_persistent(l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitTarget_x3f___spec__1___at_Lean_Meta_splitTarget_x3f___spec__2___closed__1);
l_Lean_Meta_splitLocalDecl_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_splitLocalDecl_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_splitLocalDecl_x3f___lambda__1___closed__1);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_3263_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
