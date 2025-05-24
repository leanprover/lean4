// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SearchM
// Imports: Lean.Util.ForEachExpr Lean.Meta.Tactic.Grind.Types
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedChoice;
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__18;
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_getLast___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__3;
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___closed__1;
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectFVars_visit___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run_x27___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__23;
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instMonadLiftGoalMSearchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__6;
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__2;
static lean_object* l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectFVars_visit___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__2;
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___spec__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM(lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__2;
lean_object* l_Std_Queue_empty(lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__11;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_EMatch_instInhabitedState___spec__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assignFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__16;
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__15;
lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__4;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__24;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__3;
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__8;
static lean_object* l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__4;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__12;
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__17;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__1;
static lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__9;
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2___closed__1;
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_ForEachExpr_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1;
static size_t l_Lean_Meta_Grind_instInhabitedChoice___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_mkChoice___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_Split_instInhabitedState___spec__1;
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__22;
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_ForEachExpr_visit___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__3;
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__5;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__20;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__19;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Meta_Grind_liftGoalM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1(lean_object*);
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__1;
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedEMatchTheorems___spec__1;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__7;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__7;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_num_indices(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__10;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__1;
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__1;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedGoal___spec__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instMonadLiftGoalMSearchM(lean_object*);
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Meta_Grind_liftGoalM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__1;
lean_object* l_Lean_Meta_Grind_isInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Match_instInhabitedMatchEqnsExtState___spec__1;
size_t lean_usize_land(size_t, size_t);
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice___closed__2;
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__6() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice___closed__5;
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__4;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Meta_Grind_instInhabitedChoice___closed__6;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Queue_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice___closed__2;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedEMatchTheorems___spec__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_instInhabitedChoice___closed__7;
x_4 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_EMatch_instInhabitedState___spec__1;
x_5 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Match_instInhabitedMatchEqnsExtState___spec__1;
x_6 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set(x_6, 4, x_2);
lean_ctor_set(x_6, 5, x_2);
lean_ctor_set(x_6, 6, x_4);
lean_ctor_set(x_6, 7, x_2);
lean_ctor_set(x_6, 8, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__11;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_instInhabitedChoice___closed__2;
x_4 = l_Lean_Meta_Grind_instInhabitedChoice___closed__13;
x_5 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_Split_instInhabitedState___spec__1;
x_6 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
lean_ctor_set(x_6, 6, x_1);
lean_ctor_set(x_6, 7, x_4);
lean_ctor_set(x_6, 8, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__7;
x_3 = l_Lean_Meta_Grind_instInhabitedChoice___closed__2;
x_4 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_2);
lean_ctor_set(x_4, 5, x_2);
lean_ctor_set(x_4, 6, x_2);
lean_ctor_set(x_4, 7, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_Grind_instInhabitedChoice___closed__7;
x_4 = l_Lean_Meta_Grind_instInhabitedChoice___closed__2;
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState___spec__1;
x_8 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_4);
lean_ctor_set(x_8, 5, x_3);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_3);
lean_ctor_set(x_8, 8, x_3);
lean_ctor_set(x_8, 9, x_3);
lean_ctor_set(x_8, 10, x_1);
lean_ctor_set(x_8, 11, x_3);
lean_ctor_set(x_8, 12, x_3);
lean_ctor_set(x_8, 13, x_5);
lean_ctor_set(x_8, 14, x_2);
lean_ctor_set(x_8, 15, x_4);
lean_ctor_set(x_8, 16, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*17, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice___closed__4;
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__2;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice___closed__15;
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__16;
x_3 = l_Lean_Meta_Grind_instInhabitedChoice___closed__17;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Match_instInhabitedMatchEqnsExtState___spec__1;
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__3;
x_3 = l_Lean_Meta_Grind_instInhabitedChoice___closed__2;
x_4 = l_Lean_Meta_Grind_instInhabitedChoice___closed__7;
x_5 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedGoal___spec__1;
x_6 = l_Lean_Meta_Grind_instInhabitedChoice___closed__4;
x_7 = 0;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Meta_Grind_instInhabitedChoice___closed__8;
x_10 = l_Lean_Meta_Grind_instInhabitedChoice___closed__10;
x_11 = l_Lean_Meta_Grind_instInhabitedChoice___closed__14;
x_12 = l_Lean_Meta_Grind_instInhabitedChoice___closed__18;
x_13 = l_Lean_Meta_Grind_instInhabitedChoice___closed__19;
x_14 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set(x_14, 4, x_3);
lean_ctor_set(x_14, 5, x_5);
lean_ctor_set(x_14, 6, x_3);
lean_ctor_set(x_14, 7, x_6);
lean_ctor_set(x_14, 8, x_8);
lean_ctor_set(x_14, 9, x_9);
lean_ctor_set(x_14, 10, x_4);
lean_ctor_set(x_14, 11, x_3);
lean_ctor_set(x_14, 12, x_10);
lean_ctor_set(x_14, 13, x_11);
lean_ctor_set(x_14, 14, x_12);
lean_ctor_set(x_14, 15, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*16, x_7);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__21;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__22;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedChoice___closed__20;
x_3 = l_Lean_Meta_Grind_instInhabitedChoice___closed__23;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice___closed__24;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
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
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_1);
x_16 = lean_st_ref_set(x_2, x_12, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_st_ref_set(x_2, x_24, x_13);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_setGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_withCurrGoalContext___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Meta_Grind_liftGoalM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_10(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_17 = lean_apply_9(x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_18);
lean_ctor_set(x_20, 0, x_13);
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
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_13);
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
lean_inc(x_30);
x_32 = lean_apply_9(x_1, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_30, x_34);
lean_dec(x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_43 = x_32;
} else {
 lean_dec_ref(x_32);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at_Lean_Meta_Grind_liftGoalM___spec__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_17, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_23 = lean_st_ref_take(x_2, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_22);
x_28 = lean_st_ref_set(x_2, x_24, x_25);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_21);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_st_ref_set(x_2, x_34, x_25);
lean_dec(x_2);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_StateRefT_x27_get___at_Lean_Meta_Grind_liftGoalM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_StateRefT_x27_get___at_Lean_Meta_Grind_liftGoalM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_liftGoalM___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instMonadLiftGoalMSearchM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_17, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_23 = lean_st_ref_take(x_2, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_22);
x_28 = lean_st_ref_set(x_2, x_24, x_25);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_21);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_st_ref_set(x_2, x_34, x_25);
lean_dec(x_2);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instMonadLiftGoalMSearchM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instMonadLiftGoalMSearchM___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_mk_ref(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_2);
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_2, x_13);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___rarg___lambda__1___boxed), 9, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___rarg___lambda__2), 10, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_GoalM_run_x27___spec__1___rarg), 10, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_GoalM_run___spec__1___rarg(x_11, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_SearchM_run___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_9, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_19, 7);
x_25 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_24, x_1, x_2);
lean_ctor_set(x_19, 7, x_25);
x_26 = lean_st_ref_set(x_9, x_18, x_20);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_st_ref_get(x_15, x_28);
lean_dec(x_15);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_box(0);
lean_ctor_set(x_26, 1, x_32);
lean_ctor_set(x_26, 0, x_33);
lean_ctor_set(x_30, 0, x_26);
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
x_36 = lean_box(0);
lean_ctor_set(x_26, 1, x_34);
lean_ctor_set(x_26, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_st_ref_get(x_15, x_38);
lean_dec(x_15);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_46 = lean_ctor_get(x_19, 0);
x_47 = lean_ctor_get(x_19, 1);
x_48 = lean_ctor_get(x_19, 2);
x_49 = lean_ctor_get(x_19, 3);
x_50 = lean_ctor_get(x_19, 4);
x_51 = lean_ctor_get(x_19, 5);
x_52 = lean_ctor_get(x_19, 6);
x_53 = lean_ctor_get(x_19, 7);
x_54 = lean_ctor_get(x_19, 8);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_19);
x_55 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_53, x_1, x_2);
x_56 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_47);
lean_ctor_set(x_56, 2, x_48);
lean_ctor_set(x_56, 3, x_49);
lean_ctor_set(x_56, 4, x_50);
lean_ctor_set(x_56, 5, x_51);
lean_ctor_set(x_56, 6, x_52);
lean_ctor_set(x_56, 7, x_55);
lean_ctor_set(x_56, 8, x_54);
lean_ctor_set(x_18, 0, x_56);
x_57 = lean_st_ref_set(x_9, x_18, x_20);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_st_ref_get(x_15, x_58);
lean_dec(x_15);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_59;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_67 = lean_ctor_get(x_18, 1);
x_68 = lean_ctor_get(x_18, 2);
x_69 = lean_ctor_get(x_18, 3);
x_70 = lean_ctor_get(x_18, 4);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_18);
x_71 = lean_ctor_get(x_19, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_19, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_19, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_19, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_19, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_19, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_19, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_19, 7);
lean_inc(x_78);
x_79 = lean_ctor_get(x_19, 8);
lean_inc(x_79);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 lean_ctor_release(x_19, 4);
 lean_ctor_release(x_19, 5);
 lean_ctor_release(x_19, 6);
 lean_ctor_release(x_19, 7);
 lean_ctor_release(x_19, 8);
 x_80 = x_19;
} else {
 lean_dec_ref(x_19);
 x_80 = lean_box(0);
}
x_81 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_78, x_1, x_2);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 9, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_72);
lean_ctor_set(x_82, 2, x_73);
lean_ctor_set(x_82, 3, x_74);
lean_ctor_set(x_82, 4, x_75);
lean_ctor_set(x_82, 5, x_76);
lean_ctor_set(x_82, 6, x_77);
lean_ctor_set(x_82, 7, x_81);
lean_ctor_set(x_82, 8, x_79);
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_67);
lean_ctor_set(x_83, 2, x_68);
lean_ctor_set(x_83, 3, x_69);
lean_ctor_set(x_83, 4, x_70);
x_84 = lean_st_ref_set(x_9, x_83, x_20);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_st_ref_get(x_15, x_85);
lean_dec(x_15);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_86;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_88);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
return x_93;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1___lambda__1___boxed), 12, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_3);
x_19 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_18, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_st_ref_take(x_3, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
lean_ctor_set(x_25, 0, x_23);
x_29 = lean_st_ref_set(x_3, x_25, x_26);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_22);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_st_ref_set(x_3, x_35, x_26);
lean_dec(x_3);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_19);
if (x_40 == 0)
{
return x_19;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__1;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__2;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__3;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__4;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Grind_mkChoice___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__5;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Grind_isInconsistent(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_st_ref_get(x_13, x_17);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_15, 1, x_20);
lean_ctor_set(x_18, 0, x_15);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_15, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_st_ref_get(x_13, x_25);
lean_dec(x_13);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_27);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkChoice___lambda__1___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_2 = l_Lean_Meta_Grind_mkChoice___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("!( __do_lift._@.Lean.Meta.Tactic.Grind.SearchM._hyg.361.0 )\n  ", 62, 62);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_mkChoice___closed__3;
x_2 = l_Lean_Meta_Grind_mkChoice___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.SearchM", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.mkChoice", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_mkChoice___closed__6;
x_2 = l_Lean_Meta_Grind_mkChoice___closed__7;
x_3 = lean_unsigned_to_nat(69u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Meta_Grind_mkChoice___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_mkChoice___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_23 = lean_st_ref_take(x_4, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_22);
x_28 = lean_st_ref_set(x_4, x_24, x_25);
x_29 = lean_unbox(x_21);
lean_dec(x_21);
if (x_29 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_4);
x_35 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_34, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_take(x_4, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
uint8_t x_44; lean_object* x_45; uint8_t x_46; 
x_44 = 1;
lean_ctor_set_uint8(x_39, sizeof(void*)*16, x_44);
x_45 = lean_st_ref_set(x_4, x_38, x_40);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
x_54 = lean_ctor_get(x_39, 2);
x_55 = lean_ctor_get(x_39, 3);
x_56 = lean_ctor_get(x_39, 4);
x_57 = lean_ctor_get(x_39, 5);
x_58 = lean_ctor_get(x_39, 6);
x_59 = lean_ctor_get(x_39, 7);
x_60 = lean_ctor_get(x_39, 8);
x_61 = lean_ctor_get(x_39, 9);
x_62 = lean_ctor_get(x_39, 10);
x_63 = lean_ctor_get(x_39, 11);
x_64 = lean_ctor_get(x_39, 12);
x_65 = lean_ctor_get(x_39, 13);
x_66 = lean_ctor_get(x_39, 14);
x_67 = lean_ctor_get(x_39, 15);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
x_68 = 1;
x_69 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_69, 0, x_52);
lean_ctor_set(x_69, 1, x_53);
lean_ctor_set(x_69, 2, x_54);
lean_ctor_set(x_69, 3, x_55);
lean_ctor_set(x_69, 4, x_56);
lean_ctor_set(x_69, 5, x_57);
lean_ctor_set(x_69, 6, x_58);
lean_ctor_set(x_69, 7, x_59);
lean_ctor_set(x_69, 8, x_60);
lean_ctor_set(x_69, 9, x_61);
lean_ctor_set(x_69, 10, x_62);
lean_ctor_set(x_69, 11, x_63);
lean_ctor_set(x_69, 12, x_64);
lean_ctor_set(x_69, 13, x_65);
lean_ctor_set(x_69, 14, x_66);
lean_ctor_set(x_69, 15, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*16, x_68);
lean_ctor_set(x_38, 0, x_69);
x_70 = lean_st_ref_set(x_4, x_38, x_40);
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
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
lean_dec(x_38);
x_76 = lean_ctor_get(x_39, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_39, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_39, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_39, 7);
lean_inc(x_83);
x_84 = lean_ctor_get(x_39, 8);
lean_inc(x_84);
x_85 = lean_ctor_get(x_39, 9);
lean_inc(x_85);
x_86 = lean_ctor_get(x_39, 10);
lean_inc(x_86);
x_87 = lean_ctor_get(x_39, 11);
lean_inc(x_87);
x_88 = lean_ctor_get(x_39, 12);
lean_inc(x_88);
x_89 = lean_ctor_get(x_39, 13);
lean_inc(x_89);
x_90 = lean_ctor_get(x_39, 14);
lean_inc(x_90);
x_91 = lean_ctor_get(x_39, 15);
lean_inc(x_91);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 lean_ctor_release(x_39, 7);
 lean_ctor_release(x_39, 8);
 lean_ctor_release(x_39, 9);
 lean_ctor_release(x_39, 10);
 lean_ctor_release(x_39, 11);
 lean_ctor_release(x_39, 12);
 lean_ctor_release(x_39, 13);
 lean_ctor_release(x_39, 14);
 lean_ctor_release(x_39, 15);
 x_92 = x_39;
} else {
 lean_dec_ref(x_39);
 x_92 = lean_box(0);
}
x_93 = 1;
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 16, 1);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_76);
lean_ctor_set(x_94, 1, x_77);
lean_ctor_set(x_94, 2, x_78);
lean_ctor_set(x_94, 3, x_79);
lean_ctor_set(x_94, 4, x_80);
lean_ctor_set(x_94, 5, x_81);
lean_ctor_set(x_94, 6, x_82);
lean_ctor_set(x_94, 7, x_83);
lean_ctor_set(x_94, 8, x_84);
lean_ctor_set(x_94, 9, x_85);
lean_ctor_set(x_94, 10, x_86);
lean_ctor_set(x_94, 11, x_87);
lean_ctor_set(x_94, 12, x_88);
lean_ctor_set(x_94, 13, x_89);
lean_ctor_set(x_94, 14, x_90);
lean_ctor_set(x_94, 15, x_91);
lean_ctor_set_uint8(x_94, sizeof(void*)*16, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_75);
x_96 = lean_st_ref_set(x_4, x_95, x_40);
lean_dec(x_4);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = lean_box(0);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_4);
x_101 = !lean_is_exclusive(x_35);
if (x_101 == 0)
{
return x_35;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_35, 0);
x_103 = lean_ctor_get(x_35, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_35);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_2, 1);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_3);
x_106 = lean_ctor_get(x_28, 1);
lean_inc(x_106);
lean_dec(x_28);
x_107 = lean_ctor_get(x_2, 0);
lean_inc(x_107);
lean_dec(x_2);
x_108 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_106);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_112 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_111, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l_Lean_Meta_Grind_setGoal(x_107, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_113);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_114;
}
else
{
uint8_t x_115; 
lean_dec(x_107);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_115 = !lean_is_exclusive(x_112);
if (x_115 == 0)
{
return x_112;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_112, 0);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_112);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_28, 1);
lean_inc(x_119);
lean_dec(x_28);
x_120 = !lean_is_exclusive(x_2);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_121 = lean_ctor_get(x_2, 0);
x_122 = lean_ctor_get(x_2, 1);
lean_dec(x_122);
x_123 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_119);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_st_ref_take(x_4, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_1);
lean_ctor_set(x_129, 2, x_105);
lean_ctor_set(x_129, 3, x_3);
x_130 = !lean_is_exclusive(x_127);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_127, 1);
x_132 = lean_ctor_get(x_127, 0);
lean_dec(x_132);
lean_ctor_set(x_2, 1, x_131);
lean_ctor_set(x_2, 0, x_129);
lean_ctor_set(x_127, 1, x_2);
lean_ctor_set(x_127, 0, x_121);
x_133 = lean_st_ref_set(x_4, x_127, x_128);
lean_dec(x_4);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_dec(x_135);
x_136 = lean_box(0);
lean_ctor_set(x_133, 0, x_136);
return x_133;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
lean_dec(x_133);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_140 = lean_ctor_get(x_127, 1);
lean_inc(x_140);
lean_dec(x_127);
lean_ctor_set(x_2, 1, x_140);
lean_ctor_set(x_2, 0, x_129);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_121);
lean_ctor_set(x_141, 1, x_2);
x_142 = lean_st_ref_set(x_4, x_141, x_128);
lean_dec(x_4);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
x_145 = lean_box(0);
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_143);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_147 = lean_ctor_get(x_2, 0);
lean_inc(x_147);
lean_dec(x_2);
x_148 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_119);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_st_ref_take(x_4, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_1);
lean_ctor_set(x_154, 2, x_105);
lean_ctor_set(x_154, 3, x_3);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_156 = x_152;
} else {
 lean_dec_ref(x_152);
 x_156 = lean_box(0);
}
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_147);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_st_ref_set(x_4, x_158, x_153);
lean_dec(x_4);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
return x_163;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_ctor_get(x_28, 1);
lean_inc(x_164);
lean_dec(x_28);
x_165 = l_Lean_Meta_Grind_mkChoice___closed__8;
x_166 = l_panic___at_Lean_Meta_Grind_mkChoice___spec__2(x_165, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_ctor_get(x_24, 1);
lean_inc(x_167);
lean_dec(x_24);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_22);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_st_ref_set(x_4, x_168, x_25);
x_170 = lean_unbox(x_21);
lean_dec(x_21);
if (x_170 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_3);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
lean_dec(x_173);
lean_inc(x_4);
x_176 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_175, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_st_ref_take(x_4, x_177);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_183 = x_179;
} else {
 lean_dec_ref(x_179);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_180, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 3);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 4);
lean_inc(x_188);
x_189 = lean_ctor_get(x_180, 5);
lean_inc(x_189);
x_190 = lean_ctor_get(x_180, 6);
lean_inc(x_190);
x_191 = lean_ctor_get(x_180, 7);
lean_inc(x_191);
x_192 = lean_ctor_get(x_180, 8);
lean_inc(x_192);
x_193 = lean_ctor_get(x_180, 9);
lean_inc(x_193);
x_194 = lean_ctor_get(x_180, 10);
lean_inc(x_194);
x_195 = lean_ctor_get(x_180, 11);
lean_inc(x_195);
x_196 = lean_ctor_get(x_180, 12);
lean_inc(x_196);
x_197 = lean_ctor_get(x_180, 13);
lean_inc(x_197);
x_198 = lean_ctor_get(x_180, 14);
lean_inc(x_198);
x_199 = lean_ctor_get(x_180, 15);
lean_inc(x_199);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 lean_ctor_release(x_180, 4);
 lean_ctor_release(x_180, 5);
 lean_ctor_release(x_180, 6);
 lean_ctor_release(x_180, 7);
 lean_ctor_release(x_180, 8);
 lean_ctor_release(x_180, 9);
 lean_ctor_release(x_180, 10);
 lean_ctor_release(x_180, 11);
 lean_ctor_release(x_180, 12);
 lean_ctor_release(x_180, 13);
 lean_ctor_release(x_180, 14);
 lean_ctor_release(x_180, 15);
 x_200 = x_180;
} else {
 lean_dec_ref(x_180);
 x_200 = lean_box(0);
}
x_201 = 1;
if (lean_is_scalar(x_200)) {
 x_202 = lean_alloc_ctor(0, 16, 1);
} else {
 x_202 = x_200;
}
lean_ctor_set(x_202, 0, x_184);
lean_ctor_set(x_202, 1, x_185);
lean_ctor_set(x_202, 2, x_186);
lean_ctor_set(x_202, 3, x_187);
lean_ctor_set(x_202, 4, x_188);
lean_ctor_set(x_202, 5, x_189);
lean_ctor_set(x_202, 6, x_190);
lean_ctor_set(x_202, 7, x_191);
lean_ctor_set(x_202, 8, x_192);
lean_ctor_set(x_202, 9, x_193);
lean_ctor_set(x_202, 10, x_194);
lean_ctor_set(x_202, 11, x_195);
lean_ctor_set(x_202, 12, x_196);
lean_ctor_set(x_202, 13, x_197);
lean_ctor_set(x_202, 14, x_198);
lean_ctor_set(x_202, 15, x_199);
lean_ctor_set_uint8(x_202, sizeof(void*)*16, x_201);
if (lean_is_scalar(x_183)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_183;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_182);
x_204 = lean_st_ref_set(x_4, x_203, x_181);
lean_dec(x_4);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
x_207 = lean_box(0);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_4);
x_209 = lean_ctor_get(x_176, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_176, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_211 = x_176;
} else {
 lean_dec_ref(x_176);
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
lean_object* x_213; 
x_213 = lean_ctor_get(x_2, 1);
lean_inc(x_213);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_3);
x_214 = lean_ctor_get(x_169, 1);
lean_inc(x_214);
lean_dec(x_169);
x_215 = lean_ctor_get(x_2, 0);
lean_inc(x_215);
lean_dec(x_2);
x_216 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_214);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_220 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_219, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_218);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = l_Lean_Meta_Grind_setGoal(x_215, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_221);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_215);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_223 = lean_ctor_get(x_220, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_220, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_225 = x_220;
} else {
 lean_dec_ref(x_220);
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
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_227 = lean_ctor_get(x_169, 1);
lean_inc(x_227);
lean_dec(x_169);
x_228 = lean_ctor_get(x_2, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_229 = x_2;
} else {
 lean_dec_ref(x_2);
 x_229 = lean_box(0);
}
x_230 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_227);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_st_ref_take(x_4, x_232);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_236, 0, x_231);
lean_ctor_set(x_236, 1, x_1);
lean_ctor_set(x_236, 2, x_213);
lean_ctor_set(x_236, 3, x_3);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_238 = x_234;
} else {
 lean_dec_ref(x_234);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_229;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_228);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_st_ref_set(x_4, x_240, x_235);
lean_dec(x_4);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_243 = x_241;
} else {
 lean_dec_ref(x_241);
 x_243 = lean_box(0);
}
x_244 = lean_box(0);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_169, 1);
lean_inc(x_246);
lean_dec(x_169);
x_247 = l_Lean_Meta_Grind_mkChoice___closed__8;
x_248 = l_panic___at_Lean_Meta_Grind_mkChoice___spec__2(x_247, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_246);
return x_248;
}
}
}
else
{
uint8_t x_249; 
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
x_249 = !lean_is_exclusive(x_18);
if (x_249 == 0)
{
return x_18;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_18, 0);
x_251 = lean_ctor_get(x_18, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_18);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_mkChoice___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_MVarId_getTag(x_1, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_18);
lean_ctor_set(x_20, 0, x_13);
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
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_13);
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = l_Lean_MVarId_getTag(x_1, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_30, x_34);
lean_dec(x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_43 = x_32;
} else {
 lean_dec_ref(x_32);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_18);
lean_ctor_set(x_20, 0, x_13);
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
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_13);
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = l_Lean_MVarId_getType(x_1, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_30, x_34);
lean_dec(x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_43 = x_32;
} else {
 lean_dec_ref(x_32);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_8, x_9, x_10, x_11, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_17, 1, x_22);
lean_ctor_set(x_20, 0, x_17);
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
lean_ctor_set(x_17, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_st_ref_get(x_15, x_27);
lean_dec(x_15);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__1___boxed), 11, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_18, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_st_ref_take(x_2, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
lean_ctor_set(x_25, 0, x_23);
x_29 = lean_st_ref_set(x_2, x_25, x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__2___boxed), 11, 1);
lean_closure_set(x_31, 0, x_11);
x_32 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_32, 0, x_13);
lean_closure_set(x_32, 1, x_31);
x_33 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_37 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_36, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_st_ref_take(x_2, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
lean_ctor_set(x_43, 0, x_41);
x_47 = lean_st_ref_set(x_2, x_43, x_44);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__3___boxed), 12, 2);
lean_closure_set(x_49, 0, x_40);
lean_closure_set(x_49, 1, x_22);
x_50 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_50, 0, x_13);
lean_closure_set(x_50, 1, x_49);
x_51 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_2);
x_55 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_54, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_st_ref_take(x_2, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
lean_ctor_set(x_61, 0, x_59);
x_65 = lean_st_ref_set(x_2, x_61, x_62);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
x_68 = l_Lean_Expr_mvarId_x21(x_58);
lean_dec(x_58);
lean_ctor_set(x_65, 0, x_68);
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = l_Lean_Expr_mvarId_x21(x_58);
lean_dec(x_58);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_61, 1);
lean_inc(x_72);
lean_dec(x_61);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_st_ref_set(x_2, x_73, x_62);
lean_dec(x_2);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = l_Lean_Expr_mvarId_x21(x_58);
lean_dec(x_58);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_55);
if (x_79 == 0)
{
return x_55;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_55, 0);
x_81 = lean_ctor_get(x_55, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_55);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_83 = lean_ctor_get(x_43, 1);
lean_inc(x_83);
lean_dec(x_43);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_41);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_st_ref_set(x_2, x_84, x_44);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__3___boxed), 12, 2);
lean_closure_set(x_87, 0, x_40);
lean_closure_set(x_87, 1, x_22);
x_88 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_88, 0, x_13);
lean_closure_set(x_88, 1, x_87);
x_89 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_86);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_2);
x_93 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_92, x_88, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_st_ref_take(x_2, x_95);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_st_ref_set(x_2, x_103, x_100);
lean_dec(x_2);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = l_Lean_Expr_mvarId_x21(x_96);
lean_dec(x_96);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_2);
x_109 = lean_ctor_get(x_93, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_93, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_111 = x_93;
} else {
 lean_dec_ref(x_93);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_37);
if (x_113 == 0)
{
return x_37;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_37, 0);
x_115 = lean_ctor_get(x_37, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_37);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_117 = lean_ctor_get(x_25, 1);
lean_inc(x_117);
lean_dec(x_25);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_23);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_st_ref_set(x_2, x_118, x_26);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__2___boxed), 11, 1);
lean_closure_set(x_121, 0, x_11);
x_122 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_122, 0, x_13);
lean_closure_set(x_122, 1, x_121);
x_123 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_120);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_127 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_126, x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_st_ref_take(x_2, x_129);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
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
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_135);
x_138 = lean_st_ref_set(x_2, x_137, x_134);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__3___boxed), 12, 2);
lean_closure_set(x_140, 0, x_130);
lean_closure_set(x_140, 1, x_22);
x_141 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_141, 0, x_13);
lean_closure_set(x_141, 1, x_140);
x_142 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_139);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_2);
x_146 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_145, x_141, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_st_ref_take(x_2, x_148);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_150);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_st_ref_set(x_2, x_156, x_153);
lean_dec(x_2);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = l_Lean_Expr_mvarId_x21(x_149);
lean_dec(x_149);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_2);
x_162 = lean_ctor_get(x_146, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_146, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_164 = x_146;
} else {
 lean_dec_ref(x_146);
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
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_166 = lean_ctor_get(x_127, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_127, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_168 = x_127;
} else {
 lean_dec_ref(x_127);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_170 = !lean_is_exclusive(x_19);
if (x_170 == 0)
{
return x_19;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_19, 0);
x_172 = lean_ctor_get(x_19, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_19);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_getGoal___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__4), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__1;
x_2 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Meta_Grind_getGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__3;
x_15 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_169; uint8_t x_170; 
x_169 = lean_st_ref_get(x_3, x_9);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; size_t x_184; size_t x_185; size_t x_186; size_t x_187; size_t x_188; lean_object* x_189; lean_object* x_190; 
x_173 = lean_ctor_get(x_169, 1);
x_174 = lean_ctor_get(x_171, 1);
x_175 = lean_ctor_get(x_171, 0);
lean_dec(x_175);
x_176 = lean_array_get_size(x_174);
x_177 = l_Lean_Expr_hash(x_2);
x_178 = 32;
x_179 = lean_uint64_shift_right(x_177, x_178);
x_180 = lean_uint64_xor(x_177, x_179);
x_181 = 16;
x_182 = lean_uint64_shift_right(x_180, x_181);
x_183 = lean_uint64_xor(x_180, x_182);
x_184 = lean_uint64_to_usize(x_183);
x_185 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_186 = 1;
x_187 = lean_usize_sub(x_185, x_186);
x_188 = lean_usize_land(x_184, x_187);
x_189 = lean_array_uget(x_174, x_188);
lean_dec(x_174);
x_190 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_ForEachExpr_visit___spec__1(x_2, x_189);
lean_dec(x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
lean_free_object(x_171);
lean_free_object(x_169);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_191 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_173);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_unbox(x_193);
lean_dec(x_193);
if (x_194 == 0)
{
lean_object* x_195; uint8_t x_196; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_dec(x_191);
x_196 = !lean_is_exclusive(x_192);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 0);
lean_dec(x_197);
x_198 = lean_box(0);
lean_ctor_set(x_192, 0, x_198);
x_10 = x_192;
x_11 = x_195;
goto block_168;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_192, 1);
lean_inc(x_199);
lean_dec(x_192);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_10 = x_201;
x_11 = x_195;
goto block_168;
}
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_191, 1);
lean_inc(x_202);
lean_dec(x_191);
x_203 = lean_ctor_get(x_192, 1);
lean_inc(x_203);
lean_dec(x_192);
x_204 = lean_ctor_get(x_2, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_2, 1);
lean_inc(x_205);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_206 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_204, x_3, x_203, x_5, x_6, x_7, x_8, x_202);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_205, x_3, x_209, x_5, x_6, x_7, x_8, x_208);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_10 = x_211;
x_11 = x_212;
goto block_168;
}
else
{
uint8_t x_213; 
lean_dec(x_2);
x_213 = !lean_is_exclusive(x_210);
if (x_213 == 0)
{
return x_210;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_210, 0);
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_210);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_205);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_217 = !lean_is_exclusive(x_206);
if (x_217 == 0)
{
return x_206;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_206, 0);
x_219 = lean_ctor_get(x_206, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_206);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
case 6:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_191, 1);
lean_inc(x_221);
lean_dec(x_191);
x_222 = lean_ctor_get(x_192, 1);
lean_inc(x_222);
lean_dec(x_192);
x_223 = lean_ctor_get(x_2, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_2, 2);
lean_inc(x_224);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_225 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_223, x_3, x_222, x_5, x_6, x_7, x_8, x_221);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_224, x_3, x_228, x_5, x_6, x_7, x_8, x_227);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_10 = x_230;
x_11 = x_231;
goto block_168;
}
else
{
uint8_t x_232; 
lean_dec(x_2);
x_232 = !lean_is_exclusive(x_229);
if (x_232 == 0)
{
return x_229;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_229, 0);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_229);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_224);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_225);
if (x_236 == 0)
{
return x_225;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_225, 0);
x_238 = lean_ctor_get(x_225, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_225);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
case 7:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_240 = lean_ctor_get(x_191, 1);
lean_inc(x_240);
lean_dec(x_191);
x_241 = lean_ctor_get(x_192, 1);
lean_inc(x_241);
lean_dec(x_192);
x_242 = lean_ctor_get(x_2, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_2, 2);
lean_inc(x_243);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_244 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_242, x_3, x_241, x_5, x_6, x_7, x_8, x_240);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_243, x_3, x_247, x_5, x_6, x_7, x_8, x_246);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_10 = x_249;
x_11 = x_250;
goto block_168;
}
else
{
uint8_t x_251; 
lean_dec(x_2);
x_251 = !lean_is_exclusive(x_248);
if (x_251 == 0)
{
return x_248;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_248, 0);
x_253 = lean_ctor_get(x_248, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_248);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_243);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_255 = !lean_is_exclusive(x_244);
if (x_255 == 0)
{
return x_244;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_244, 0);
x_257 = lean_ctor_get(x_244, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_244);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
case 8:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_259 = lean_ctor_get(x_191, 1);
lean_inc(x_259);
lean_dec(x_191);
x_260 = lean_ctor_get(x_192, 1);
lean_inc(x_260);
lean_dec(x_192);
x_261 = lean_ctor_get(x_2, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_2, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_2, 3);
lean_inc(x_263);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_264 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_261, x_3, x_260, x_5, x_6, x_7, x_8, x_259);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_268 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_262, x_3, x_267, x_5, x_6, x_7, x_8, x_266);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_263, x_3, x_271, x_5, x_6, x_7, x_8, x_270);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_10 = x_273;
x_11 = x_274;
goto block_168;
}
else
{
uint8_t x_275; 
lean_dec(x_2);
x_275 = !lean_is_exclusive(x_272);
if (x_275 == 0)
{
return x_272;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_272, 0);
x_277 = lean_ctor_get(x_272, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_272);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_263);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_279 = !lean_is_exclusive(x_268);
if (x_279 == 0)
{
return x_268;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_268, 0);
x_281 = lean_ctor_get(x_268, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_268);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_283 = !lean_is_exclusive(x_264);
if (x_283 == 0)
{
return x_264;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_264, 0);
x_285 = lean_ctor_get(x_264, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_264);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
case 10:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_287 = lean_ctor_get(x_191, 1);
lean_inc(x_287);
lean_dec(x_191);
x_288 = lean_ctor_get(x_192, 1);
lean_inc(x_288);
lean_dec(x_192);
x_289 = lean_ctor_get(x_2, 1);
lean_inc(x_289);
x_290 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_289, x_3, x_288, x_5, x_6, x_7, x_8, x_287);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_10 = x_291;
x_11 = x_292;
goto block_168;
}
else
{
uint8_t x_293; 
lean_dec(x_2);
x_293 = !lean_is_exclusive(x_290);
if (x_293 == 0)
{
return x_290;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_290, 0);
x_295 = lean_ctor_get(x_290, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_290);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
case 11:
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_191, 1);
lean_inc(x_297);
lean_dec(x_191);
x_298 = lean_ctor_get(x_192, 1);
lean_inc(x_298);
lean_dec(x_192);
x_299 = lean_ctor_get(x_2, 2);
lean_inc(x_299);
x_300 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_299, x_3, x_298, x_5, x_6, x_7, x_8, x_297);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_10 = x_301;
x_11 = x_302;
goto block_168;
}
else
{
uint8_t x_303; 
lean_dec(x_2);
x_303 = !lean_is_exclusive(x_300);
if (x_303 == 0)
{
return x_300;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_300, 0);
x_305 = lean_ctor_get(x_300, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_300);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
default: 
{
lean_object* x_307; uint8_t x_308; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_307 = lean_ctor_get(x_191, 1);
lean_inc(x_307);
lean_dec(x_191);
x_308 = !lean_is_exclusive(x_192);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_192, 0);
lean_dec(x_309);
x_310 = lean_box(0);
lean_ctor_set(x_192, 0, x_310);
x_10 = x_192;
x_11 = x_307;
goto block_168;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_192, 1);
lean_inc(x_311);
lean_dec(x_192);
x_312 = lean_box(0);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_311);
x_10 = x_313;
x_11 = x_307;
goto block_168;
}
}
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_191);
if (x_314 == 0)
{
return x_191;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_191, 0);
x_316 = lean_ctor_get(x_191, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_191);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
else
{
lean_object* x_318; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_318 = lean_ctor_get(x_190, 0);
lean_inc(x_318);
lean_dec(x_190);
lean_ctor_set(x_171, 1, x_4);
lean_ctor_set(x_171, 0, x_318);
return x_169;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint64_t x_322; uint64_t x_323; uint64_t x_324; uint64_t x_325; uint64_t x_326; uint64_t x_327; uint64_t x_328; size_t x_329; size_t x_330; size_t x_331; size_t x_332; size_t x_333; lean_object* x_334; lean_object* x_335; 
x_319 = lean_ctor_get(x_169, 1);
x_320 = lean_ctor_get(x_171, 1);
lean_inc(x_320);
lean_dec(x_171);
x_321 = lean_array_get_size(x_320);
x_322 = l_Lean_Expr_hash(x_2);
x_323 = 32;
x_324 = lean_uint64_shift_right(x_322, x_323);
x_325 = lean_uint64_xor(x_322, x_324);
x_326 = 16;
x_327 = lean_uint64_shift_right(x_325, x_326);
x_328 = lean_uint64_xor(x_325, x_327);
x_329 = lean_uint64_to_usize(x_328);
x_330 = lean_usize_of_nat(x_321);
lean_dec(x_321);
x_331 = 1;
x_332 = lean_usize_sub(x_330, x_331);
x_333 = lean_usize_land(x_329, x_332);
x_334 = lean_array_uget(x_320, x_333);
lean_dec(x_320);
x_335 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_ForEachExpr_visit___spec__1(x_2, x_334);
lean_dec(x_334);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; 
lean_free_object(x_169);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_336 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_319);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_unbox(x_338);
lean_dec(x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_340 = lean_ctor_get(x_336, 1);
lean_inc(x_340);
lean_dec(x_336);
x_341 = lean_ctor_get(x_337, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_342 = x_337;
} else {
 lean_dec_ref(x_337);
 x_342 = lean_box(0);
}
x_343 = lean_box(0);
if (lean_is_scalar(x_342)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_342;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_341);
x_10 = x_344;
x_11 = x_340;
goto block_168;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_345 = lean_ctor_get(x_336, 1);
lean_inc(x_345);
lean_dec(x_336);
x_346 = lean_ctor_get(x_337, 1);
lean_inc(x_346);
lean_dec(x_337);
x_347 = lean_ctor_get(x_2, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_2, 1);
lean_inc(x_348);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_349 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_347, x_3, x_346, x_5, x_6, x_7, x_8, x_345);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_348, x_3, x_352, x_5, x_6, x_7, x_8, x_351);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_10 = x_354;
x_11 = x_355;
goto block_168;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_2);
x_356 = lean_ctor_get(x_353, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_353, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_358 = x_353;
} else {
 lean_dec_ref(x_353);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_348);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_360 = lean_ctor_get(x_349, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_349, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_362 = x_349;
} else {
 lean_dec_ref(x_349);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
case 6:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_364 = lean_ctor_get(x_336, 1);
lean_inc(x_364);
lean_dec(x_336);
x_365 = lean_ctor_get(x_337, 1);
lean_inc(x_365);
lean_dec(x_337);
x_366 = lean_ctor_get(x_2, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_2, 2);
lean_inc(x_367);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_368 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_366, x_3, x_365, x_5, x_6, x_7, x_8, x_364);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
lean_dec(x_368);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_367, x_3, x_371, x_5, x_6, x_7, x_8, x_370);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
x_10 = x_373;
x_11 = x_374;
goto block_168;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_2);
x_375 = lean_ctor_get(x_372, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_372, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_377 = x_372;
} else {
 lean_dec_ref(x_372);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_367);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_379 = lean_ctor_get(x_368, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_368, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_381 = x_368;
} else {
 lean_dec_ref(x_368);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
return x_382;
}
}
case 7:
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_383 = lean_ctor_get(x_336, 1);
lean_inc(x_383);
lean_dec(x_336);
x_384 = lean_ctor_get(x_337, 1);
lean_inc(x_384);
lean_dec(x_337);
x_385 = lean_ctor_get(x_2, 1);
lean_inc(x_385);
x_386 = lean_ctor_get(x_2, 2);
lean_inc(x_386);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_387 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_385, x_3, x_384, x_5, x_6, x_7, x_8, x_383);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_386, x_3, x_390, x_5, x_6, x_7, x_8, x_389);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_10 = x_392;
x_11 = x_393;
goto block_168;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_2);
x_394 = lean_ctor_get(x_391, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_391, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_396 = x_391;
} else {
 lean_dec_ref(x_391);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_386);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_398 = lean_ctor_get(x_387, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_387, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_400 = x_387;
} else {
 lean_dec_ref(x_387);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
case 8:
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_402 = lean_ctor_get(x_336, 1);
lean_inc(x_402);
lean_dec(x_336);
x_403 = lean_ctor_get(x_337, 1);
lean_inc(x_403);
lean_dec(x_337);
x_404 = lean_ctor_get(x_2, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_2, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_2, 3);
lean_inc(x_406);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_407 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_404, x_3, x_403, x_5, x_6, x_7, x_8, x_402);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_411 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_405, x_3, x_410, x_5, x_6, x_7, x_8, x_409);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_406, x_3, x_414, x_5, x_6, x_7, x_8, x_413);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_415, 1);
lean_inc(x_417);
lean_dec(x_415);
x_10 = x_416;
x_11 = x_417;
goto block_168;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_2);
x_418 = lean_ctor_get(x_415, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_415, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_420 = x_415;
} else {
 lean_dec_ref(x_415);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_406);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_422 = lean_ctor_get(x_411, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_411, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_424 = x_411;
} else {
 lean_dec_ref(x_411);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_426 = lean_ctor_get(x_407, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_407, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_428 = x_407;
} else {
 lean_dec_ref(x_407);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_426);
lean_ctor_set(x_429, 1, x_427);
return x_429;
}
}
case 10:
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_ctor_get(x_336, 1);
lean_inc(x_430);
lean_dec(x_336);
x_431 = lean_ctor_get(x_337, 1);
lean_inc(x_431);
lean_dec(x_337);
x_432 = lean_ctor_get(x_2, 1);
lean_inc(x_432);
x_433 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_432, x_3, x_431, x_5, x_6, x_7, x_8, x_430);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_10 = x_434;
x_11 = x_435;
goto block_168;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_2);
x_436 = lean_ctor_get(x_433, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_433, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_438 = x_433;
} else {
 lean_dec_ref(x_433);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
case 11:
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_440 = lean_ctor_get(x_336, 1);
lean_inc(x_440);
lean_dec(x_336);
x_441 = lean_ctor_get(x_337, 1);
lean_inc(x_441);
lean_dec(x_337);
x_442 = lean_ctor_get(x_2, 2);
lean_inc(x_442);
x_443 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_442, x_3, x_441, x_5, x_6, x_7, x_8, x_440);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_10 = x_444;
x_11 = x_445;
goto block_168;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_2);
x_446 = lean_ctor_get(x_443, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_443, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_448 = x_443;
} else {
 lean_dec_ref(x_443);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
default: 
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_450 = lean_ctor_get(x_336, 1);
lean_inc(x_450);
lean_dec(x_336);
x_451 = lean_ctor_get(x_337, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_452 = x_337;
} else {
 lean_dec_ref(x_337);
 x_452 = lean_box(0);
}
x_453 = lean_box(0);
if (lean_is_scalar(x_452)) {
 x_454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_454 = x_452;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_451);
x_10 = x_454;
x_11 = x_450;
goto block_168;
}
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_455 = lean_ctor_get(x_336, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_336, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_457 = x_336;
} else {
 lean_dec_ref(x_336);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_455);
lean_ctor_set(x_458, 1, x_456);
return x_458;
}
}
else
{
lean_object* x_459; lean_object* x_460; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_459 = lean_ctor_get(x_335, 0);
lean_inc(x_459);
lean_dec(x_335);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_4);
lean_ctor_set(x_169, 0, x_460);
return x_169;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint64_t x_466; uint64_t x_467; uint64_t x_468; uint64_t x_469; uint64_t x_470; uint64_t x_471; uint64_t x_472; size_t x_473; size_t x_474; size_t x_475; size_t x_476; size_t x_477; lean_object* x_478; lean_object* x_479; 
x_461 = lean_ctor_get(x_169, 0);
x_462 = lean_ctor_get(x_169, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_169);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_464 = x_461;
} else {
 lean_dec_ref(x_461);
 x_464 = lean_box(0);
}
x_465 = lean_array_get_size(x_463);
x_466 = l_Lean_Expr_hash(x_2);
x_467 = 32;
x_468 = lean_uint64_shift_right(x_466, x_467);
x_469 = lean_uint64_xor(x_466, x_468);
x_470 = 16;
x_471 = lean_uint64_shift_right(x_469, x_470);
x_472 = lean_uint64_xor(x_469, x_471);
x_473 = lean_uint64_to_usize(x_472);
x_474 = lean_usize_of_nat(x_465);
lean_dec(x_465);
x_475 = 1;
x_476 = lean_usize_sub(x_474, x_475);
x_477 = lean_usize_land(x_473, x_476);
x_478 = lean_array_uget(x_463, x_477);
lean_dec(x_463);
x_479 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_ForEachExpr_visit___spec__1(x_2, x_478);
lean_dec(x_478);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; 
lean_dec(x_464);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_480 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_462);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; uint8_t x_483; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_unbox(x_482);
lean_dec(x_482);
if (x_483 == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_484 = lean_ctor_get(x_480, 1);
lean_inc(x_484);
lean_dec(x_480);
x_485 = lean_ctor_get(x_481, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_486 = x_481;
} else {
 lean_dec_ref(x_481);
 x_486 = lean_box(0);
}
x_487 = lean_box(0);
if (lean_is_scalar(x_486)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_486;
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_485);
x_10 = x_488;
x_11 = x_484;
goto block_168;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_489 = lean_ctor_get(x_480, 1);
lean_inc(x_489);
lean_dec(x_480);
x_490 = lean_ctor_get(x_481, 1);
lean_inc(x_490);
lean_dec(x_481);
x_491 = lean_ctor_get(x_2, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_2, 1);
lean_inc(x_492);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_493 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_491, x_3, x_490, x_5, x_6, x_7, x_8, x_489);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_492, x_3, x_496, x_5, x_6, x_7, x_8, x_495);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_10 = x_498;
x_11 = x_499;
goto block_168;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_2);
x_500 = lean_ctor_get(x_497, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_497, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_502 = x_497;
} else {
 lean_dec_ref(x_497);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_492);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_504 = lean_ctor_get(x_493, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_493, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_506 = x_493;
} else {
 lean_dec_ref(x_493);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
case 6:
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_508 = lean_ctor_get(x_480, 1);
lean_inc(x_508);
lean_dec(x_480);
x_509 = lean_ctor_get(x_481, 1);
lean_inc(x_509);
lean_dec(x_481);
x_510 = lean_ctor_get(x_2, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_2, 2);
lean_inc(x_511);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_512 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_510, x_3, x_509, x_5, x_6, x_7, x_8, x_508);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_511, x_3, x_515, x_5, x_6, x_7, x_8, x_514);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 1);
lean_inc(x_518);
lean_dec(x_516);
x_10 = x_517;
x_11 = x_518;
goto block_168;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_2);
x_519 = lean_ctor_get(x_516, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_516, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_521 = x_516;
} else {
 lean_dec_ref(x_516);
 x_521 = lean_box(0);
}
if (lean_is_scalar(x_521)) {
 x_522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_522 = x_521;
}
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_520);
return x_522;
}
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_511);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_523 = lean_ctor_get(x_512, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_512, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_525 = x_512;
} else {
 lean_dec_ref(x_512);
 x_525 = lean_box(0);
}
if (lean_is_scalar(x_525)) {
 x_526 = lean_alloc_ctor(1, 2, 0);
} else {
 x_526 = x_525;
}
lean_ctor_set(x_526, 0, x_523);
lean_ctor_set(x_526, 1, x_524);
return x_526;
}
}
case 7:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_527 = lean_ctor_get(x_480, 1);
lean_inc(x_527);
lean_dec(x_480);
x_528 = lean_ctor_get(x_481, 1);
lean_inc(x_528);
lean_dec(x_481);
x_529 = lean_ctor_get(x_2, 1);
lean_inc(x_529);
x_530 = lean_ctor_get(x_2, 2);
lean_inc(x_530);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_531 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_529, x_3, x_528, x_5, x_6, x_7, x_8, x_527);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
lean_dec(x_532);
x_535 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_530, x_3, x_534, x_5, x_6, x_7, x_8, x_533);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
x_10 = x_536;
x_11 = x_537;
goto block_168;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_2);
x_538 = lean_ctor_get(x_535, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_535, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_540 = x_535;
} else {
 lean_dec_ref(x_535);
 x_540 = lean_box(0);
}
if (lean_is_scalar(x_540)) {
 x_541 = lean_alloc_ctor(1, 2, 0);
} else {
 x_541 = x_540;
}
lean_ctor_set(x_541, 0, x_538);
lean_ctor_set(x_541, 1, x_539);
return x_541;
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_530);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_542 = lean_ctor_get(x_531, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_531, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_544 = x_531;
} else {
 lean_dec_ref(x_531);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 2, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_542);
lean_ctor_set(x_545, 1, x_543);
return x_545;
}
}
case 8:
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_546 = lean_ctor_get(x_480, 1);
lean_inc(x_546);
lean_dec(x_480);
x_547 = lean_ctor_get(x_481, 1);
lean_inc(x_547);
lean_dec(x_481);
x_548 = lean_ctor_get(x_2, 1);
lean_inc(x_548);
x_549 = lean_ctor_get(x_2, 2);
lean_inc(x_549);
x_550 = lean_ctor_get(x_2, 3);
lean_inc(x_550);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_551 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_548, x_3, x_547, x_5, x_6, x_7, x_8, x_546);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_555 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_549, x_3, x_554, x_5, x_6, x_7, x_8, x_553);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_550, x_3, x_558, x_5, x_6, x_7, x_8, x_557);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_10 = x_560;
x_11 = x_561;
goto block_168;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec(x_2);
x_562 = lean_ctor_get(x_559, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_559, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_564 = x_559;
} else {
 lean_dec_ref(x_559);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_565 = lean_alloc_ctor(1, 2, 0);
} else {
 x_565 = x_564;
}
lean_ctor_set(x_565, 0, x_562);
lean_ctor_set(x_565, 1, x_563);
return x_565;
}
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_550);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_566 = lean_ctor_get(x_555, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_555, 1);
lean_inc(x_567);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_568 = x_555;
} else {
 lean_dec_ref(x_555);
 x_568 = lean_box(0);
}
if (lean_is_scalar(x_568)) {
 x_569 = lean_alloc_ctor(1, 2, 0);
} else {
 x_569 = x_568;
}
lean_ctor_set(x_569, 0, x_566);
lean_ctor_set(x_569, 1, x_567);
return x_569;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_570 = lean_ctor_get(x_551, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_551, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 x_572 = x_551;
} else {
 lean_dec_ref(x_551);
 x_572 = lean_box(0);
}
if (lean_is_scalar(x_572)) {
 x_573 = lean_alloc_ctor(1, 2, 0);
} else {
 x_573 = x_572;
}
lean_ctor_set(x_573, 0, x_570);
lean_ctor_set(x_573, 1, x_571);
return x_573;
}
}
case 10:
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_574 = lean_ctor_get(x_480, 1);
lean_inc(x_574);
lean_dec(x_480);
x_575 = lean_ctor_get(x_481, 1);
lean_inc(x_575);
lean_dec(x_481);
x_576 = lean_ctor_get(x_2, 1);
lean_inc(x_576);
x_577 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_576, x_3, x_575, x_5, x_6, x_7, x_8, x_574);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec(x_577);
x_10 = x_578;
x_11 = x_579;
goto block_168;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_2);
x_580 = lean_ctor_get(x_577, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_577, 1);
lean_inc(x_581);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_582 = x_577;
} else {
 lean_dec_ref(x_577);
 x_582 = lean_box(0);
}
if (lean_is_scalar(x_582)) {
 x_583 = lean_alloc_ctor(1, 2, 0);
} else {
 x_583 = x_582;
}
lean_ctor_set(x_583, 0, x_580);
lean_ctor_set(x_583, 1, x_581);
return x_583;
}
}
case 11:
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_584 = lean_ctor_get(x_480, 1);
lean_inc(x_584);
lean_dec(x_480);
x_585 = lean_ctor_get(x_481, 1);
lean_inc(x_585);
lean_dec(x_481);
x_586 = lean_ctor_get(x_2, 2);
lean_inc(x_586);
x_587 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_586, x_3, x_585, x_5, x_6, x_7, x_8, x_584);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; 
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec(x_587);
x_10 = x_588;
x_11 = x_589;
goto block_168;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_2);
x_590 = lean_ctor_get(x_587, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_587, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_592 = x_587;
} else {
 lean_dec_ref(x_587);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_590);
lean_ctor_set(x_593, 1, x_591);
return x_593;
}
}
default: 
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_594 = lean_ctor_get(x_480, 1);
lean_inc(x_594);
lean_dec(x_480);
x_595 = lean_ctor_get(x_481, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_596 = x_481;
} else {
 lean_dec_ref(x_481);
 x_596 = lean_box(0);
}
x_597 = lean_box(0);
if (lean_is_scalar(x_596)) {
 x_598 = lean_alloc_ctor(0, 2, 0);
} else {
 x_598 = x_596;
}
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_595);
x_10 = x_598;
x_11 = x_594;
goto block_168;
}
}
}
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_599 = lean_ctor_get(x_480, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_480, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_601 = x_480;
} else {
 lean_dec_ref(x_480);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_599);
lean_ctor_set(x_602, 1, x_600);
return x_602;
}
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_603 = lean_ctor_get(x_479, 0);
lean_inc(x_603);
lean_dec(x_479);
if (lean_is_scalar(x_464)) {
 x_604 = lean_alloc_ctor(0, 2, 0);
} else {
 x_604 = x_464;
}
lean_ctor_set(x_604, 0, x_603);
lean_ctor_set(x_604, 1, x_4);
x_605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_462);
return x_605;
}
}
block_168:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_st_ref_take(x_3, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; uint8_t x_34; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_array_get_size(x_19);
x_21 = l_Lean_Expr_hash(x_2);
x_22 = 32;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = 16;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = lean_uint64_to_usize(x_27);
x_29 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_30 = 1;
x_31 = lean_usize_sub(x_29, x_30);
x_32 = lean_usize_land(x_28, x_31);
x_33 = lean_array_uget(x_19, x_32);
x_34 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectFVars_visit___spec__1(x_2, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_18, x_35);
lean_dec(x_18);
lean_inc(x_13);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_13);
lean_ctor_set(x_37, 2, x_33);
x_38 = lean_array_uset(x_19, x_32, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectFVars_visit___spec__2(x_38);
lean_ctor_set(x_15, 1, x_45);
lean_ctor_set(x_15, 0, x_36);
x_46 = lean_st_ref_set(x_3, x_15, x_16);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_10);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_ctor_set(x_15, 1, x_38);
lean_ctor_set(x_15, 0, x_36);
x_51 = lean_st_ref_set(x_3, x_15, x_16);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_10);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_box(0);
x_57 = lean_array_uset(x_19, x_32, x_56);
lean_inc(x_13);
x_58 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_ForEachExpr_visit___spec__6(x_2, x_13, x_33);
x_59 = lean_array_uset(x_57, x_32, x_58);
lean_ctor_set(x_15, 1, x_59);
x_60 = lean_st_ref_set(x_3, x_15, x_16);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_10);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_10);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; size_t x_75; size_t x_76; size_t x_77; size_t x_78; size_t x_79; lean_object* x_80; uint8_t x_81; 
x_65 = lean_ctor_get(x_15, 0);
x_66 = lean_ctor_get(x_15, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_15);
x_67 = lean_array_get_size(x_66);
x_68 = l_Lean_Expr_hash(x_2);
x_69 = 32;
x_70 = lean_uint64_shift_right(x_68, x_69);
x_71 = lean_uint64_xor(x_68, x_70);
x_72 = 16;
x_73 = lean_uint64_shift_right(x_71, x_72);
x_74 = lean_uint64_xor(x_71, x_73);
x_75 = lean_uint64_to_usize(x_74);
x_76 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_77 = 1;
x_78 = lean_usize_sub(x_76, x_77);
x_79 = lean_usize_land(x_75, x_78);
x_80 = lean_array_uget(x_66, x_79);
x_81 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectFVars_visit___spec__1(x_2, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_65, x_82);
lean_dec(x_65);
lean_inc(x_13);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_13);
lean_ctor_set(x_84, 2, x_80);
x_85 = lean_array_uset(x_66, x_79, x_84);
x_86 = lean_unsigned_to_nat(4u);
x_87 = lean_nat_mul(x_83, x_86);
x_88 = lean_unsigned_to_nat(3u);
x_89 = lean_nat_div(x_87, x_88);
lean_dec(x_87);
x_90 = lean_array_get_size(x_85);
x_91 = lean_nat_dec_le(x_89, x_90);
lean_dec(x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectFVars_visit___spec__2(x_85);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_83);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_st_ref_set(x_3, x_93, x_16);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_10);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_85);
x_99 = lean_st_ref_set(x_3, x_98, x_16);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_10);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_box(0);
x_104 = lean_array_uset(x_66, x_79, x_103);
lean_inc(x_13);
x_105 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_ForEachExpr_visit___spec__6(x_2, x_13, x_80);
x_106 = lean_array_uset(x_104, x_79, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_65);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_st_ref_set(x_3, x_107, x_16);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_10);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint64_t x_121; uint64_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; size_t x_128; size_t x_129; size_t x_130; size_t x_131; size_t x_132; lean_object* x_133; uint8_t x_134; 
x_112 = lean_ctor_get(x_10, 0);
x_113 = lean_ctor_get(x_10, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_10);
x_114 = lean_st_ref_take(x_3, x_11);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_119 = x_115;
} else {
 lean_dec_ref(x_115);
 x_119 = lean_box(0);
}
x_120 = lean_array_get_size(x_118);
x_121 = l_Lean_Expr_hash(x_2);
x_122 = 32;
x_123 = lean_uint64_shift_right(x_121, x_122);
x_124 = lean_uint64_xor(x_121, x_123);
x_125 = 16;
x_126 = lean_uint64_shift_right(x_124, x_125);
x_127 = lean_uint64_xor(x_124, x_126);
x_128 = lean_uint64_to_usize(x_127);
x_129 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_130 = 1;
x_131 = lean_usize_sub(x_129, x_130);
x_132 = lean_usize_land(x_128, x_131);
x_133 = lean_array_uget(x_118, x_132);
x_134 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectFVars_visit___spec__1(x_2, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_add(x_117, x_135);
lean_dec(x_117);
lean_inc(x_112);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_2);
lean_ctor_set(x_137, 1, x_112);
lean_ctor_set(x_137, 2, x_133);
x_138 = lean_array_uset(x_118, x_132, x_137);
x_139 = lean_unsigned_to_nat(4u);
x_140 = lean_nat_mul(x_136, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = lean_array_get_size(x_138);
x_144 = lean_nat_dec_le(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectFVars_visit___spec__2(x_138);
if (lean_is_scalar(x_119)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_119;
}
lean_ctor_set(x_146, 0, x_136);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_st_ref_set(x_3, x_146, x_116);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_112);
lean_ctor_set(x_150, 1, x_113);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
if (lean_is_scalar(x_119)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_119;
}
lean_ctor_set(x_152, 0, x_136);
lean_ctor_set(x_152, 1, x_138);
x_153 = lean_st_ref_set(x_3, x_152, x_116);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_112);
lean_ctor_set(x_156, 1, x_113);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_box(0);
x_159 = lean_array_uset(x_118, x_132, x_158);
lean_inc(x_112);
x_160 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_ForEachExpr_visit___spec__6(x_2, x_112, x_133);
x_161 = lean_array_uset(x_159, x_132, x_160);
if (lean_is_scalar(x_119)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_119;
}
lean_ctor_set(x_162, 0, x_117);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_st_ref_set(x_3, x_162, x_116);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_112);
lean_ctor_set(x_166, 1, x_113);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_165;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_164);
return x_167;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_FVarId_getDecl(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_LocalDecl_index(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = l_Lean_LocalDecl_index(x_18);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_3, 0);
x_30 = l_Lean_LocalDecl_index(x_28);
lean_dec(x_28);
x_31 = lean_nat_dec_le(x_29, x_30);
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_10, 0, x_34);
return x_10;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_29);
lean_ctor_set(x_3, 0, x_30);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_10, 0, x_37);
return x_10;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_10, 0);
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
lean_dec(x_3);
x_40 = l_Lean_LocalDecl_index(x_38);
lean_dec(x_38);
x_41 = lean_nat_dec_le(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_10, 0, x_45);
return x_10;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_40);
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_10, 0, x_49);
return x_10;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_10, 0);
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_10);
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_53 = x_3;
} else {
 lean_dec_ref(x_3);
 x_53 = lean_box(0);
}
x_54 = l_Lean_LocalDecl_index(x_50);
lean_dec(x_50);
x_55 = lean_nat_dec_le(x_52, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_54);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_52);
x_57 = 0;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_51);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_52);
if (lean_is_scalar(x_53)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_53;
}
lean_ctor_set(x_61, 0, x_54);
x_62 = 0;
x_63 = lean_box(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_51);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_10);
if (x_66 == 0)
{
return x_10;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_10, 0);
x_68 = lean_ctor_get(x_10, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_10);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_4);
lean_dec(x_1);
x_70 = 1;
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_3);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_8);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasFVar(x_1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__1(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__2___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_box(0);
x_8 = l_Lean_Meta_Grind_instInhabitedChoice___closed__13;
x_9 = lean_st_mk_ref(x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1;
x_13 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_12, x_1, x_10, x_7, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_10, x_15);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExpr_visit___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 1, x_15);
x_16 = lean_st_ref_set(x_1, x_11, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_st_ref_set(x_1, x_25, x_12);
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
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_MVarId_assignFalseProof(x_1, x_2, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_14, 1, x_24);
lean_ctor_set(x_14, 0, x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_14);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = l_Lean_MVarId_assignFalseProof(x_1, x_2, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
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
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_2, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_List_isEmpty___rarg(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_11);
x_17 = l_List_getLast___rarg(x_15, lean_box(0));
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_1);
x_21 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_20);
x_23 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_26, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_take(x_2, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
lean_ctor_set(x_32, 0, x_30);
x_36 = lean_st_ref_set(x_2, x_32, x_33);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_30);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_st_ref_set(x_2, x_40, x_33);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_27);
if (x_44 == 0)
{
return x_27;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_27, 0);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_27);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
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
x_48 = lean_box(0);
lean_ctor_set(x_11, 0, x_48);
return x_11;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_List_isEmpty___rarg(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = l_List_getLast___rarg(x_51, lean_box(0));
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_56, 0, x_55);
lean_closure_set(x_56, 1, x_1);
x_57 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_58 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_58, 0, x_57);
lean_closure_set(x_58, 1, x_56);
x_59 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_63 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_62, x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_st_ref_take(x_2, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
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
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_st_ref_set(x_2, x_72, x_69);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_74);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_ctor_get(x_63, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_63, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_78 = x_63;
} else {
 lean_dec_ref(x_63);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_51);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_50);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
lean_ctor_set(x_2, 0, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_22, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_1);
x_11 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_19);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_17, 3);
x_33 = lean_ctor_get(x_17, 2);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_ctor_set(x_17, 2, x_36);
x_37 = lean_st_ref_take(x_3, x_11);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
lean_ctor_set(x_18, 1, x_30);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_37, 1, x_18);
lean_ctor_set(x_37, 0, x_35);
x_41 = lean_st_ref_set(x_3, x_37, x_39);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_32);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_2, 0, x_45);
lean_ctor_set(x_41, 0, x_2);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_32);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_2, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_2);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_37, 1);
lean_inc(x_50);
lean_dec(x_37);
lean_ctor_set(x_18, 1, x_30);
lean_ctor_set(x_18, 0, x_17);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_18);
x_52 = lean_st_ref_set(x_3, x_51, x_50);
lean_dec(x_3);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_32);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_2, 0, x_56);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_ctor_get(x_18, 0);
x_59 = lean_ctor_get(x_18, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_18);
lean_inc(x_32);
lean_ctor_set(x_17, 2, x_59);
x_60 = lean_st_ref_take(x_3, x_11);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_17);
lean_ctor_set(x_63, 1, x_30);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_st_ref_set(x_3, x_64, x_61);
lean_dec(x_3);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_32);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_2, 0, x_69);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_71 = lean_ctor_get(x_17, 0);
x_72 = lean_ctor_get(x_17, 1);
x_73 = lean_ctor_get(x_17, 3);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_17);
x_74 = lean_ctor_get(x_18, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_76 = x_18;
} else {
 lean_dec_ref(x_18);
 x_76 = lean_box(0);
}
lean_inc(x_73);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_72);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_73);
x_78 = lean_st_ref_take(x_3, x_11);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_30);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_st_ref_set(x_3, x_82, x_79);
lean_dec(x_3);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_73);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_2, 0, x_87);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_2);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
}
}
}
else
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
lean_dec(x_2);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_90 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_11);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 2);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec(x_89);
x_96 = lean_ctor_get(x_93, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_99 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_98, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_1);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_95);
x_2 = x_101;
x_11 = x_100;
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_95);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_105 = x_99;
} else {
 lean_dec_ref(x_99);
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
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_107 = lean_ctor_get(x_89, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_93, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_93, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_93, 3);
lean_inc(x_110);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 x_111 = x_93;
} else {
 lean_dec_ref(x_93);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_94, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_94, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_114 = x_94;
} else {
 lean_dec_ref(x_94);
 x_114 = lean_box(0);
}
lean_inc(x_110);
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(0, 4, 0);
} else {
 x_115 = x_111;
}
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_109);
lean_ctor_set(x_115, 2, x_113);
lean_ctor_set(x_115, 3, x_110);
x_116 = lean_st_ref_take(x_3, x_11);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_114;
}
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_107);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_112);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_st_ref_set(x_3, x_120, x_117);
lean_dec(x_3);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_110);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_89);
if (lean_is_scalar(x_123)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_123;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_122);
return x_127;
}
}
}
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__4;
x_3 = l_instInhabitedOfMonad___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2___closed__1;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.SearchM.0.Lean.Meta.Grind.nextChronoGoal\?", 73, 73);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_mkChoice___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(151u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__3;
x_12 = l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1(x_15, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1;
x_21 = lean_box(0);
x_22 = lean_apply_10(x_20, x_21, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1(x_34, x_35, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1;
x_41 = lean_box(0);
x_42 = lean_apply_10(x_40, x_41, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_49 = x_36;
} else {
 lean_dec_ref(x_36);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Expr_isFalse(x_9);
x_11 = lean_box(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = l_Lean_Expr_isFalse(x_12);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesOn", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__3;
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Expr_isAppOfArity(x_9, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__5;
x_20 = l_Lean_Expr_isAppOfArity(x_9, x_19, x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_9);
x_21 = lean_box(0);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_dec(x_11);
x_27 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__3;
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Expr_isAppOfArity(x_9, x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__5;
x_31 = l_Lean_Expr_isAppOfArity(x_9, x_30, x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_9);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_26);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_11, 0);
lean_dec(x_41);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_11, 0, x_42);
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_9);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = l_Lean_Expr_mvar___override(x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_7, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_13, x_18);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_15, 1, x_22);
lean_ctor_set(x_15, 0, x_19);
lean_ctor_set(x_20, 0, x_15);
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
lean_ctor_set(x_15, 1, x_23);
lean_ctor_set(x_15, 0, x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_13, x_27);
lean_dec(x_13);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_8, x_15);
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
lean_ctor_set(x_17, 0, x_1);
x_21 = lean_st_ref_set(x_8, x_17, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_st_ref_get(x_14, x_23);
lean_dec(x_14);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_box(0);
lean_ctor_set(x_21, 1, x_27);
lean_ctor_set(x_21, 0, x_28);
lean_ctor_set(x_25, 0, x_21);
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
x_31 = lean_box(0);
lean_ctor_set(x_21, 1, x_29);
lean_ctor_set(x_21, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_st_ref_get(x_14, x_33);
lean_dec(x_14);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_41 = lean_ctor_get(x_17, 1);
x_42 = lean_ctor_get(x_17, 2);
x_43 = lean_ctor_get(x_17, 3);
x_44 = lean_ctor_get(x_17, 4);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
lean_ctor_set(x_45, 4, x_44);
x_46 = lean_st_ref_set(x_8, x_45, x_18);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_st_ref_get(x_14, x_47);
lean_dec(x_14);
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
x_53 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_48;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
}
static lean_object* _init_l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__1___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_2 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_23 = lean_st_ref_take(x_2, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_22);
x_28 = lean_st_ref_set(x_2, x_24, x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_instantiateMVarsCore(x_21, x_1);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__2___boxed), 11, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_35 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_33);
x_36 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_2);
x_40 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_39, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_st_ref_take(x_2, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
lean_ctor_set(x_45, 0, x_43);
x_49 = lean_st_ref_set(x_2, x_45, x_46);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_31);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec(x_45);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_st_ref_set(x_2, x_55, x_46);
lean_dec(x_2);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_31);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_31);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_40);
if (x_60 == 0)
{
return x_40;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_40, 0);
x_62 = lean_ctor_get(x_40, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_40);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_64 = lean_ctor_get(x_24, 1);
lean_inc(x_64);
lean_dec(x_24);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_22);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_st_ref_set(x_2, x_65, x_25);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_instantiateMVarsCore(x_21, x_1);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__2___boxed), 11, 1);
lean_closure_set(x_71, 0, x_70);
x_72 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_73 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_73, 0, x_72);
lean_closure_set(x_73, 1, x_71);
x_74 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_2);
x_78 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_77, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_st_ref_take(x_2, x_80);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_st_ref_set(x_2, x_87, x_84);
lean_dec(x_2);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_69);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_69);
lean_dec(x_2);
x_92 = lean_ctor_get(x_78, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_94 = x_78;
} else {
 lean_dec_ref(x_78);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_18);
if (x_96 == 0)
{
return x_18;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_18, 0);
x_98 = lean_ctor_get(x_18, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_18);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_MVarId_getDecl(x_1, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_18);
lean_ctor_set(x_20, 0, x_13);
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
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_13);
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = l_Lean_MVarId_getDecl(x_1, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_30, x_34);
lean_dec(x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_43 = x_32;
} else {
 lean_dec_ref(x_32);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(x_1, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_18);
lean_ctor_set(x_20, 0, x_13);
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
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_13);
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(x_1, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_30, x_34);
lean_dec(x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_43 = x_32;
} else {
 lean_dec_ref(x_32);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f(x_1, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_18);
lean_ctor_set(x_20, 0, x_13);
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
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_13);
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f(x_1, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_30, x_34);
lean_dec(x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_43 = x_32;
} else {
 lean_dec_ref(x_32);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__3___boxed), 11, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
x_18 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_17, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_23 = lean_st_ref_take(x_3, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_22);
x_28 = lean_st_ref_set(x_3, x_24, x_25);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_21);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_st_ref_set(x_3, x_34, x_25);
lean_dec(x_3);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 1);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_34, 0, x_39);
x_13 = x_34;
goto block_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_29);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
x_13 = x_44;
goto block_28;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_32);
x_47 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_29, 1, x_50);
x_51 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_29);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
x_13 = x_54;
goto block_28;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_29, 1);
x_56 = lean_ctor_get(x_31, 0);
lean_inc(x_56);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 1);
x_60 = lean_ctor_get(x_31, 1);
lean_inc(x_60);
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 1);
x_64 = lean_ctor_get(x_56, 2);
x_65 = lean_ctor_get(x_56, 3);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_inc(x_66);
x_67 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1___boxed), 11, 1);
lean_closure_set(x_67, 0, x_66);
lean_inc(x_1);
x_68 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_68, 0, x_1);
lean_closure_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_73 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_72, x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_st_ref_take(x_4, x_75);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
lean_ctor_set(x_79, 0, x_77);
x_83 = lean_st_ref_set(x_4, x_79, x_80);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_83, 1);
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
lean_dec(x_76);
x_88 = lean_local_ctx_num_indices(x_87);
x_89 = lean_nat_dec_lt(x_59, x_88);
lean_dec(x_88);
if (x_89 == 0)
{
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_90; 
lean_free_object(x_83);
lean_free_object(x_56);
lean_dec(x_65);
lean_dec(x_62);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_90 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_85);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_91);
lean_inc(x_66);
x_93 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_66, x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
lean_inc(x_66);
x_95 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_95, 0, x_66);
lean_inc(x_1);
x_96 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_96, 0, x_1);
lean_closure_set(x_96, 1, x_95);
x_97 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_94);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_101 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_100, x_96, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_st_ref_take(x_4, x_103);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_110 = lean_ctor_get(x_107, 0);
lean_dec(x_110);
lean_ctor_set(x_107, 0, x_105);
x_111 = lean_st_ref_set(x_4, x_107, x_108);
x_112 = lean_unbox(x_104);
lean_dec(x_104);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_91);
lean_dec(x_66);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_st_ref_take(x_4, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_115, 1);
lean_dec(x_118);
lean_ctor_set(x_115, 1, x_60);
x_119 = lean_st_ref_set(x_4, x_115, x_116);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_119, 1);
x_122 = lean_ctor_get(x_119, 0);
lean_dec(x_122);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_123 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_121);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_119, 1, x_29);
lean_ctor_set(x_119, 0, x_126);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_119);
lean_ctor_set(x_123, 0, x_127);
x_13 = x_123;
goto block_28;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_123, 0);
x_129 = lean_ctor_get(x_123, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_123);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_119, 1, x_29);
lean_ctor_set(x_119, 0, x_130);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_119);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
x_13 = x_132;
goto block_28;
}
}
else
{
uint8_t x_133; 
lean_free_object(x_119);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_133 = !lean_is_exclusive(x_123);
if (x_133 == 0)
{
x_13 = x_123;
goto block_28;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_123, 0);
x_135 = lean_ctor_get(x_123, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_123);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_13 = x_136;
goto block_28;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_119, 1);
lean_inc(x_137);
lean_dec(x_119);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_138 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_139);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_29);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
if (lean_is_scalar(x_141)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_141;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_140);
x_13 = x_145;
goto block_28;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_146 = lean_ctor_get(x_138, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_138, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_148 = x_138;
} else {
 lean_dec_ref(x_138);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
x_13 = x_149;
goto block_28;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_150 = lean_ctor_get(x_115, 0);
lean_inc(x_150);
lean_dec(x_115);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_60);
x_152 = lean_st_ref_set(x_4, x_151, x_116);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_155 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_153);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_156);
if (lean_is_scalar(x_154)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_154;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_29);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
if (lean_is_scalar(x_158)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_158;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_157);
x_13 = x_162;
goto block_28;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_154);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_163 = lean_ctor_get(x_155, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_155, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_165 = x_155;
} else {
 lean_dec_ref(x_155);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
x_13 = x_166;
goto block_28;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_58);
x_167 = !lean_is_exclusive(x_111);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_111, 1);
x_169 = lean_ctor_get(x_111, 0);
lean_dec(x_169);
lean_inc(x_1);
lean_inc(x_91);
x_170 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__4), 11, 2);
lean_closure_set(x_170, 0, x_91);
lean_closure_set(x_170, 1, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_171 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_66, x_170, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_168);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_60);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_91);
x_174 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_173);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_174, 0);
lean_dec(x_176);
lean_ctor_set(x_55, 0, x_91);
x_177 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_177);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_111);
lean_ctor_set(x_174, 0, x_178);
x_13 = x_174;
goto block_28;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_174, 1);
lean_inc(x_179);
lean_dec(x_174);
lean_ctor_set(x_55, 0, x_91);
x_180 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_180);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_111);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_179);
x_13 = x_182;
goto block_28;
}
}
else
{
uint8_t x_183; 
lean_free_object(x_111);
lean_dec(x_91);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_183 = !lean_is_exclusive(x_174);
if (x_183 == 0)
{
x_13 = x_174;
goto block_28;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_174, 0);
x_185 = lean_ctor_get(x_174, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_174);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_13 = x_186;
goto block_28;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_59);
lean_dec(x_31);
x_187 = !lean_is_exclusive(x_171);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_171, 0);
lean_dec(x_188);
x_189 = !lean_is_exclusive(x_172);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_172, 0);
lean_ctor_set(x_55, 1, x_190);
lean_ctor_set(x_55, 0, x_91);
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_172, 0, x_111);
x_13 = x_171;
goto block_28;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_172, 0);
lean_inc(x_191);
lean_dec(x_172);
lean_ctor_set(x_55, 1, x_191);
lean_ctor_set(x_55, 0, x_91);
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_2);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_111);
lean_ctor_set(x_171, 0, x_192);
x_13 = x_171;
goto block_28;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_171, 1);
lean_inc(x_193);
lean_dec(x_171);
x_194 = lean_ctor_get(x_172, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_195 = x_172;
} else {
 lean_dec_ref(x_172);
 x_195 = lean_box(0);
}
lean_ctor_set(x_55, 1, x_194);
lean_ctor_set(x_55, 0, x_91);
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
lean_ctor_set(x_111, 1, x_29);
lean_ctor_set(x_111, 0, x_2);
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 1, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_111);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_193);
x_13 = x_197;
goto block_28;
}
}
}
else
{
uint8_t x_198; 
lean_free_object(x_111);
lean_dec(x_91);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_198 = !lean_is_exclusive(x_171);
if (x_198 == 0)
{
x_13 = x_171;
goto block_28;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_171, 0);
x_200 = lean_ctor_get(x_171, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_171);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_13 = x_201;
goto block_28;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_111, 1);
lean_inc(x_202);
lean_dec(x_111);
lean_inc(x_1);
lean_inc(x_91);
x_203 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__4), 11, 2);
lean_closure_set(x_203, 0, x_91);
lean_closure_set(x_203, 1, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_204 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_66, x_203, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_202);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_60);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_91);
x_207 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
lean_ctor_set(x_55, 0, x_91);
x_210 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_29);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
if (lean_is_scalar(x_209)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_209;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_208);
x_13 = x_213;
goto block_28;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_91);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_214 = lean_ctor_get(x_207, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_207, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_216 = x_207;
} else {
 lean_dec_ref(x_207);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
x_13 = x_217;
goto block_28;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_59);
lean_dec(x_31);
x_218 = lean_ctor_get(x_204, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_219 = x_204;
} else {
 lean_dec_ref(x_204);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_205, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 x_221 = x_205;
} else {
 lean_dec_ref(x_205);
 x_221 = lean_box(0);
}
lean_ctor_set(x_55, 1, x_220);
lean_ctor_set(x_55, 0, x_91);
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_2);
lean_ctor_set(x_222, 1, x_29);
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_222);
if (lean_is_scalar(x_219)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_219;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_218);
x_13 = x_224;
goto block_28;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_91);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_225 = lean_ctor_get(x_204, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_204, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_227 = x_204;
} else {
 lean_dec_ref(x_204);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
x_13 = x_228;
goto block_28;
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_229 = lean_ctor_get(x_107, 1);
lean_inc(x_229);
lean_dec(x_107);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_105);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_st_ref_set(x_4, x_230, x_108);
x_232 = lean_unbox(x_104);
lean_dec(x_104);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_91);
lean_dec(x_66);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_st_ref_take(x_4, x_233);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_60);
x_240 = lean_st_ref_set(x_4, x_239, x_236);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_242 = x_240;
} else {
 lean_dec_ref(x_240);
 x_242 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_243 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_241);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_244);
if (lean_is_scalar(x_242)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_242;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_29);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
if (lean_is_scalar(x_246)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_246;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_245);
x_13 = x_250;
goto block_28;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_242);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_251 = lean_ctor_get(x_243, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_243, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_253 = x_243;
} else {
 lean_dec_ref(x_243);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
x_13 = x_254;
goto block_28;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_58);
x_255 = lean_ctor_get(x_231, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_256 = x_231;
} else {
 lean_dec_ref(x_231);
 x_256 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_91);
x_257 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__4), 11, 2);
lean_closure_set(x_257, 0, x_91);
lean_closure_set(x_257, 1, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_258 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_66, x_257, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_255);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_60);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_91);
x_261 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
lean_ctor_set(x_55, 0, x_91);
x_264 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_256)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_256;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_29);
x_266 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_266, 0, x_265);
if (lean_is_scalar(x_263)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_263;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_262);
x_13 = x_267;
goto block_28;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_256);
lean_dec(x_91);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_268 = lean_ctor_get(x_261, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_261, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_270 = x_261;
} else {
 lean_dec_ref(x_261);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
x_13 = x_271;
goto block_28;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_59);
lean_dec(x_31);
x_272 = lean_ctor_get(x_258, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_273 = x_258;
} else {
 lean_dec_ref(x_258);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_259, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_275 = x_259;
} else {
 lean_dec_ref(x_259);
 x_275 = lean_box(0);
}
lean_ctor_set(x_55, 1, x_274);
lean_ctor_set(x_55, 0, x_91);
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
if (lean_is_scalar(x_256)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_256;
}
lean_ctor_set(x_276, 0, x_2);
lean_ctor_set(x_276, 1, x_29);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_275;
}
lean_ctor_set(x_277, 0, x_276);
if (lean_is_scalar(x_273)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_273;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_272);
x_13 = x_278;
goto block_28;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_256);
lean_dec(x_91);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_279 = lean_ctor_get(x_258, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_258, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_281 = x_258;
} else {
 lean_dec_ref(x_258);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
x_13 = x_282;
goto block_28;
}
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_91);
lean_dec(x_66);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_283 = !lean_is_exclusive(x_101);
if (x_283 == 0)
{
x_13 = x_101;
goto block_28;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_101, 0);
x_285 = lean_ctor_get(x_101, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_101);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_13 = x_286;
goto block_28;
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_91);
lean_dec(x_66);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_287 = !lean_is_exclusive(x_93);
if (x_287 == 0)
{
x_13 = x_93;
goto block_28;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_93, 0);
x_289 = lean_ctor_get(x_93, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_93);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
x_13 = x_290;
goto block_28;
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_66);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_291 = !lean_is_exclusive(x_90);
if (x_291 == 0)
{
x_13 = x_90;
goto block_28;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_90, 0);
x_293 = lean_ctor_get(x_90, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_90);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_13 = x_294;
goto block_28;
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_66);
x_295 = !lean_is_exclusive(x_64);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_296 = lean_ctor_get(x_64, 0);
x_297 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_ctor_set(x_56, 2, x_297);
x_298 = lean_st_ref_take(x_4, x_85);
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_300 = lean_ctor_get(x_298, 1);
x_301 = lean_ctor_get(x_298, 0);
lean_dec(x_301);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_298, 1, x_64);
lean_ctor_set(x_298, 0, x_296);
x_302 = lean_st_ref_set(x_4, x_298, x_300);
x_303 = !lean_is_exclusive(x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_302, 0);
lean_dec(x_304);
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_65);
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_83, 1, x_29);
lean_ctor_set(x_83, 0, x_306);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_83);
lean_ctor_set(x_302, 0, x_307);
x_13 = x_302;
goto block_28;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_308 = lean_ctor_get(x_302, 1);
lean_inc(x_308);
lean_dec(x_302);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_65);
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_83, 1, x_29);
lean_ctor_set(x_83, 0, x_310);
x_311 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_311, 0, x_83);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_308);
x_13 = x_312;
goto block_28;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_313 = lean_ctor_get(x_298, 1);
lean_inc(x_313);
lean_dec(x_298);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 0, x_56);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_296);
lean_ctor_set(x_314, 1, x_64);
x_315 = lean_st_ref_set(x_4, x_314, x_313);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_65);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_83, 1, x_29);
lean_ctor_set(x_83, 0, x_319);
x_320 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_320, 0, x_83);
if (lean_is_scalar(x_317)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_317;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_316);
x_13 = x_321;
goto block_28;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_322 = lean_ctor_get(x_64, 0);
x_323 = lean_ctor_get(x_64, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_64);
lean_inc(x_65);
lean_ctor_set(x_56, 2, x_323);
x_324 = lean_st_ref_take(x_4, x_85);
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_326 = x_324;
} else {
 lean_dec_ref(x_324);
 x_326 = lean_box(0);
}
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_56);
lean_ctor_set(x_327, 1, x_60);
if (lean_is_scalar(x_326)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_326;
}
lean_ctor_set(x_328, 0, x_322);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_st_ref_set(x_4, x_328, x_325);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_331 = x_329;
} else {
 lean_dec_ref(x_329);
 x_331 = lean_box(0);
}
x_332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_332, 0, x_65);
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_83, 1, x_29);
lean_ctor_set(x_83, 0, x_333);
x_334 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_334, 0, x_83);
if (lean_is_scalar(x_331)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_331;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_330);
x_13 = x_335;
goto block_28;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_free_object(x_83);
lean_free_object(x_56);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_31);
lean_inc(x_58);
x_336 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_336, 0, x_66);
lean_closure_set(x_336, 1, x_58);
lean_inc(x_1);
x_337 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_337, 0, x_1);
lean_closure_set(x_337, 1, x_336);
x_338 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_85);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
lean_dec(x_339);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_342 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_341, x_337, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_340);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_st_ref_take(x_4, x_344);
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
lean_object* x_348; uint8_t x_349; 
x_348 = lean_ctor_get(x_346, 0);
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_350 = lean_ctor_get(x_346, 1);
x_351 = lean_ctor_get(x_348, 0);
lean_dec(x_351);
lean_ctor_set(x_348, 0, x_345);
x_352 = lean_st_ref_set(x_4, x_348, x_350);
x_353 = !lean_is_exclusive(x_352);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_352, 0);
lean_dec(x_354);
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
lean_ctor_set(x_346, 1, x_29);
lean_ctor_set(x_346, 0, x_2);
x_355 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_355, 0, x_346);
lean_ctor_set(x_352, 0, x_355);
x_13 = x_352;
goto block_28;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
lean_dec(x_352);
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
lean_ctor_set(x_346, 1, x_29);
lean_ctor_set(x_346, 0, x_2);
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_346);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
x_13 = x_358;
goto block_28;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_359 = lean_ctor_get(x_346, 1);
x_360 = lean_ctor_get(x_348, 1);
lean_inc(x_360);
lean_dec(x_348);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_345);
lean_ctor_set(x_361, 1, x_360);
x_362 = lean_st_ref_set(x_4, x_361, x_359);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_364 = x_362;
} else {
 lean_dec_ref(x_362);
 x_364 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
lean_ctor_set(x_346, 1, x_29);
lean_ctor_set(x_346, 0, x_2);
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_346);
if (lean_is_scalar(x_364)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_364;
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_363);
x_13 = x_366;
goto block_28;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_367 = lean_ctor_get(x_346, 0);
x_368 = lean_ctor_get(x_346, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_346);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_370 = x_367;
} else {
 lean_dec_ref(x_367);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_345);
lean_ctor_set(x_371, 1, x_369);
x_372 = lean_st_ref_set(x_4, x_371, x_368);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_2);
lean_ctor_set(x_375, 1, x_29);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_375);
if (lean_is_scalar(x_374)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_374;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_373);
x_13 = x_377;
goto block_28;
}
}
else
{
uint8_t x_378; 
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
x_378 = !lean_is_exclusive(x_342);
if (x_378 == 0)
{
x_13 = x_342;
goto block_28;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_342, 0);
x_380 = lean_ctor_get(x_342, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_342);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
x_13 = x_381;
goto block_28;
}
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_382 = lean_ctor_get(x_83, 1);
lean_inc(x_382);
lean_dec(x_83);
x_383 = lean_ctor_get(x_76, 1);
lean_inc(x_383);
lean_dec(x_76);
x_384 = lean_local_ctx_num_indices(x_383);
x_385 = lean_nat_dec_lt(x_59, x_384);
lean_dec(x_384);
if (x_385 == 0)
{
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_386; 
lean_free_object(x_56);
lean_dec(x_65);
lean_dec(x_62);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_386 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_382);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_387);
lean_inc(x_66);
x_389 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_66, x_387, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_388);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
lean_dec(x_389);
lean_inc(x_66);
x_391 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_391, 0, x_66);
lean_inc(x_1);
x_392 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_392, 0, x_1);
lean_closure_set(x_392, 1, x_391);
x_393 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_390);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_ctor_get(x_394, 0);
lean_inc(x_396);
lean_dec(x_394);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_397 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_396, x_392, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_395);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_ctor_get(x_398, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_398, 1);
lean_inc(x_401);
lean_dec(x_398);
x_402 = lean_st_ref_take(x_4, x_399);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_406 = x_403;
} else {
 lean_dec_ref(x_403);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_401);
lean_ctor_set(x_407, 1, x_405);
x_408 = lean_st_ref_set(x_4, x_407, x_404);
x_409 = lean_unbox(x_400);
lean_dec(x_400);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_387);
lean_dec(x_66);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_st_ref_take(x_4, x_410);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_ctor_get(x_412, 0);
lean_inc(x_414);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_415 = x_412;
} else {
 lean_dec_ref(x_412);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_60);
x_417 = lean_st_ref_set(x_4, x_416, x_413);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_419 = x_417;
} else {
 lean_dec_ref(x_417);
 x_419 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_420 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_418);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_423 = x_420;
} else {
 lean_dec_ref(x_420);
 x_423 = lean_box(0);
}
x_424 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_424, 0, x_421);
if (lean_is_scalar(x_419)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_419;
}
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_29);
x_426 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_426, 0, x_425);
if (lean_is_scalar(x_423)) {
 x_427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_427 = x_423;
}
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_422);
x_13 = x_427;
goto block_28;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_419);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_428 = lean_ctor_get(x_420, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_420, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_430 = x_420;
} else {
 lean_dec_ref(x_420);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_428);
lean_ctor_set(x_431, 1, x_429);
x_13 = x_431;
goto block_28;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_58);
x_432 = lean_ctor_get(x_408, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_433 = x_408;
} else {
 lean_dec_ref(x_408);
 x_433 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_387);
x_434 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__4), 11, 2);
lean_closure_set(x_434, 0, x_387);
lean_closure_set(x_434, 1, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_435 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_66, x_434, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_432);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; 
lean_dec(x_60);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_387);
x_438 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_387, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_437);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_440 = x_438;
} else {
 lean_dec_ref(x_438);
 x_440 = lean_box(0);
}
lean_ctor_set(x_55, 0, x_387);
x_441 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_433)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_433;
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_29);
x_443 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_443, 0, x_442);
if (lean_is_scalar(x_440)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_440;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_439);
x_13 = x_444;
goto block_28;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_433);
lean_dec(x_387);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_445 = lean_ctor_get(x_438, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_438, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_447 = x_438;
} else {
 lean_dec_ref(x_438);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
x_13 = x_448;
goto block_28;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_59);
lean_dec(x_31);
x_449 = lean_ctor_get(x_435, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_450 = x_435;
} else {
 lean_dec_ref(x_435);
 x_450 = lean_box(0);
}
x_451 = lean_ctor_get(x_436, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_452 = x_436;
} else {
 lean_dec_ref(x_436);
 x_452 = lean_box(0);
}
lean_ctor_set(x_55, 1, x_451);
lean_ctor_set(x_55, 0, x_387);
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
if (lean_is_scalar(x_433)) {
 x_453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_453 = x_433;
}
lean_ctor_set(x_453, 0, x_2);
lean_ctor_set(x_453, 1, x_29);
if (lean_is_scalar(x_452)) {
 x_454 = lean_alloc_ctor(1, 1, 0);
} else {
 x_454 = x_452;
}
lean_ctor_set(x_454, 0, x_453);
if (lean_is_scalar(x_450)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_450;
}
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_449);
x_13 = x_455;
goto block_28;
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_433);
lean_dec(x_387);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_456 = lean_ctor_get(x_435, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_435, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_458 = x_435;
} else {
 lean_dec_ref(x_435);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_456);
lean_ctor_set(x_459, 1, x_457);
x_13 = x_459;
goto block_28;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_387);
lean_dec(x_66);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_460 = lean_ctor_get(x_397, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_397, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_462 = x_397;
} else {
 lean_dec_ref(x_397);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_461);
x_13 = x_463;
goto block_28;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_387);
lean_dec(x_66);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_464 = lean_ctor_get(x_389, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_389, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_466 = x_389;
} else {
 lean_dec_ref(x_389);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_464);
lean_ctor_set(x_467, 1, x_465);
x_13 = x_467;
goto block_28;
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_66);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_468 = lean_ctor_get(x_386, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_386, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_470 = x_386;
} else {
 lean_dec_ref(x_386);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set(x_471, 1, x_469);
x_13 = x_471;
goto block_28;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec(x_66);
x_472 = lean_ctor_get(x_64, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_64, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_474 = x_64;
} else {
 lean_dec_ref(x_64);
 x_474 = lean_box(0);
}
lean_inc(x_65);
lean_ctor_set(x_56, 2, x_473);
x_475 = lean_st_ref_take(x_4, x_382);
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_477 = x_475;
} else {
 lean_dec_ref(x_475);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_474;
}
lean_ctor_set(x_478, 0, x_56);
lean_ctor_set(x_478, 1, x_60);
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_472);
lean_ctor_set(x_479, 1, x_478);
x_480 = lean_st_ref_set(x_4, x_479, x_476);
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_482 = x_480;
} else {
 lean_dec_ref(x_480);
 x_482 = lean_box(0);
}
x_483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_483, 0, x_65);
x_484 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_484, 0, x_483);
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_29);
x_486 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_486, 0, x_485);
if (lean_is_scalar(x_482)) {
 x_487 = lean_alloc_ctor(0, 2, 0);
} else {
 x_487 = x_482;
}
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_481);
x_13 = x_487;
goto block_28;
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_free_object(x_56);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_31);
lean_inc(x_58);
x_488 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_488, 0, x_66);
lean_closure_set(x_488, 1, x_58);
lean_inc(x_1);
x_489 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_489, 0, x_1);
lean_closure_set(x_489, 1, x_488);
x_490 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_382);
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
x_493 = lean_ctor_get(x_491, 0);
lean_inc(x_493);
lean_dec(x_491);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_494 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_493, x_489, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_492);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_498 = lean_st_ref_take(x_4, x_496);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_501 = x_498;
} else {
 lean_dec_ref(x_498);
 x_501 = lean_box(0);
}
x_502 = lean_ctor_get(x_499, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_503 = x_499;
} else {
 lean_dec_ref(x_499);
 x_503 = lean_box(0);
}
if (lean_is_scalar(x_503)) {
 x_504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_504 = x_503;
}
lean_ctor_set(x_504, 0, x_497);
lean_ctor_set(x_504, 1, x_502);
x_505 = lean_st_ref_set(x_4, x_504, x_500);
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_507 = x_505;
} else {
 lean_dec_ref(x_505);
 x_507 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
if (lean_is_scalar(x_501)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_501;
}
lean_ctor_set(x_508, 0, x_2);
lean_ctor_set(x_508, 1, x_29);
x_509 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_509, 0, x_508);
if (lean_is_scalar(x_507)) {
 x_510 = lean_alloc_ctor(0, 2, 0);
} else {
 x_510 = x_507;
}
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_506);
x_13 = x_510;
goto block_28;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
x_511 = lean_ctor_get(x_494, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_494, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_513 = x_494;
} else {
 lean_dec_ref(x_494);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_512);
x_13 = x_514;
goto block_28;
}
}
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
x_515 = lean_ctor_get(x_79, 1);
lean_inc(x_515);
lean_dec(x_79);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_77);
lean_ctor_set(x_516, 1, x_515);
x_517 = lean_st_ref_set(x_4, x_516, x_80);
x_518 = lean_ctor_get(x_517, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 lean_ctor_release(x_517, 1);
 x_519 = x_517;
} else {
 lean_dec_ref(x_517);
 x_519 = lean_box(0);
}
x_520 = lean_ctor_get(x_76, 1);
lean_inc(x_520);
lean_dec(x_76);
x_521 = lean_local_ctx_num_indices(x_520);
x_522 = lean_nat_dec_lt(x_59, x_521);
lean_dec(x_521);
if (x_522 == 0)
{
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_523; 
lean_dec(x_519);
lean_free_object(x_56);
lean_dec(x_65);
lean_dec(x_62);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_523 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_518);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_524);
lean_inc(x_66);
x_526 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_66, x_524, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_525);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_527 = lean_ctor_get(x_526, 1);
lean_inc(x_527);
lean_dec(x_526);
lean_inc(x_66);
x_528 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_528, 0, x_66);
lean_inc(x_1);
x_529 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_529, 0, x_1);
lean_closure_set(x_529, 1, x_528);
x_530 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_527);
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = lean_ctor_get(x_531, 0);
lean_inc(x_533);
lean_dec(x_531);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_534 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_533, x_529, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_532);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_537 = lean_ctor_get(x_535, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_535, 1);
lean_inc(x_538);
lean_dec(x_535);
x_539 = lean_st_ref_take(x_4, x_536);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_543 = x_540;
} else {
 lean_dec_ref(x_540);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_538);
lean_ctor_set(x_544, 1, x_542);
x_545 = lean_st_ref_set(x_4, x_544, x_541);
x_546 = lean_unbox(x_537);
lean_dec(x_537);
if (x_546 == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_524);
lean_dec(x_66);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
lean_dec(x_545);
x_548 = lean_st_ref_take(x_4, x_547);
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_551 = lean_ctor_get(x_549, 0);
lean_inc(x_551);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_552 = x_549;
} else {
 lean_dec_ref(x_549);
 x_552 = lean_box(0);
}
if (lean_is_scalar(x_552)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_552;
}
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_60);
x_554 = lean_st_ref_set(x_4, x_553, x_550);
x_555 = lean_ctor_get(x_554, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_556 = x_554;
} else {
 lean_dec_ref(x_554);
 x_556 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_557 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_555);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_560 = x_557;
} else {
 lean_dec_ref(x_557);
 x_560 = lean_box(0);
}
x_561 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_561, 0, x_558);
if (lean_is_scalar(x_556)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_556;
}
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_29);
x_563 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_563, 0, x_562);
if (lean_is_scalar(x_560)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_560;
}
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_559);
x_13 = x_564;
goto block_28;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_556);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_565 = lean_ctor_get(x_557, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_557, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_567 = x_557;
} else {
 lean_dec_ref(x_557);
 x_567 = lean_box(0);
}
if (lean_is_scalar(x_567)) {
 x_568 = lean_alloc_ctor(1, 2, 0);
} else {
 x_568 = x_567;
}
lean_ctor_set(x_568, 0, x_565);
lean_ctor_set(x_568, 1, x_566);
x_13 = x_568;
goto block_28;
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
lean_dec(x_58);
x_569 = lean_ctor_get(x_545, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_570 = x_545;
} else {
 lean_dec_ref(x_545);
 x_570 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_524);
x_571 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__4), 11, 2);
lean_closure_set(x_571, 0, x_524);
lean_closure_set(x_571, 1, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_572 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_66, x_571, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_569);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; 
lean_dec(x_60);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_524);
x_575 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_524, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_574);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_576 = lean_ctor_get(x_575, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_577 = x_575;
} else {
 lean_dec_ref(x_575);
 x_577 = lean_box(0);
}
lean_ctor_set(x_55, 0, x_524);
x_578 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_570)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_570;
}
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_29);
x_580 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_580, 0, x_579);
if (lean_is_scalar(x_577)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_577;
}
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_576);
x_13 = x_581;
goto block_28;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_570);
lean_dec(x_524);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_582 = lean_ctor_get(x_575, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_575, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_584 = x_575;
} else {
 lean_dec_ref(x_575);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_582);
lean_ctor_set(x_585, 1, x_583);
x_13 = x_585;
goto block_28;
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_59);
lean_dec(x_31);
x_586 = lean_ctor_get(x_572, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_587 = x_572;
} else {
 lean_dec_ref(x_572);
 x_587 = lean_box(0);
}
x_588 = lean_ctor_get(x_573, 0);
lean_inc(x_588);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 x_589 = x_573;
} else {
 lean_dec_ref(x_573);
 x_589 = lean_box(0);
}
lean_ctor_set(x_55, 1, x_588);
lean_ctor_set(x_55, 0, x_524);
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
if (lean_is_scalar(x_570)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_570;
}
lean_ctor_set(x_590, 0, x_2);
lean_ctor_set(x_590, 1, x_29);
if (lean_is_scalar(x_589)) {
 x_591 = lean_alloc_ctor(1, 1, 0);
} else {
 x_591 = x_589;
}
lean_ctor_set(x_591, 0, x_590);
if (lean_is_scalar(x_587)) {
 x_592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_592 = x_587;
}
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_586);
x_13 = x_592;
goto block_28;
}
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_570);
lean_dec(x_524);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_593 = lean_ctor_get(x_572, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_572, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_595 = x_572;
} else {
 lean_dec_ref(x_572);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_593);
lean_ctor_set(x_596, 1, x_594);
x_13 = x_596;
goto block_28;
}
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_524);
lean_dec(x_66);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_597 = lean_ctor_get(x_534, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_534, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_599 = x_534;
} else {
 lean_dec_ref(x_534);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(1, 2, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_597);
lean_ctor_set(x_600, 1, x_598);
x_13 = x_600;
goto block_28;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_524);
lean_dec(x_66);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_601 = lean_ctor_get(x_526, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_526, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_603 = x_526;
} else {
 lean_dec_ref(x_526);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_601);
lean_ctor_set(x_604, 1, x_602);
x_13 = x_604;
goto block_28;
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
lean_dec(x_66);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_605 = lean_ctor_get(x_523, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_523, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_607 = x_523;
} else {
 lean_dec_ref(x_523);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_607)) {
 x_608 = lean_alloc_ctor(1, 2, 0);
} else {
 x_608 = x_607;
}
lean_ctor_set(x_608, 0, x_605);
lean_ctor_set(x_608, 1, x_606);
x_13 = x_608;
goto block_28;
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_66);
x_609 = lean_ctor_get(x_64, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_64, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_611 = x_64;
} else {
 lean_dec_ref(x_64);
 x_611 = lean_box(0);
}
lean_inc(x_65);
lean_ctor_set(x_56, 2, x_610);
x_612 = lean_st_ref_take(x_4, x_518);
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_614 = x_612;
} else {
 lean_dec_ref(x_612);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_615 = lean_alloc_ctor(1, 2, 0);
} else {
 x_615 = x_611;
}
lean_ctor_set(x_615, 0, x_56);
lean_ctor_set(x_615, 1, x_60);
if (lean_is_scalar(x_614)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_614;
}
lean_ctor_set(x_616, 0, x_609);
lean_ctor_set(x_616, 1, x_615);
x_617 = lean_st_ref_set(x_4, x_616, x_613);
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_619 = x_617;
} else {
 lean_dec_ref(x_617);
 x_619 = lean_box(0);
}
x_620 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_620, 0, x_65);
x_621 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_621, 0, x_620);
if (lean_is_scalar(x_519)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_519;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_29);
x_623 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_623, 0, x_622);
if (lean_is_scalar(x_619)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_619;
}
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_618);
x_13 = x_624;
goto block_28;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_519);
lean_free_object(x_56);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_31);
lean_inc(x_58);
x_625 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_625, 0, x_66);
lean_closure_set(x_625, 1, x_58);
lean_inc(x_1);
x_626 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_626, 0, x_1);
lean_closure_set(x_626, 1, x_625);
x_627 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_518);
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
lean_dec(x_627);
x_630 = lean_ctor_get(x_628, 0);
lean_inc(x_630);
lean_dec(x_628);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_631 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_630, x_626, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_629);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
lean_dec(x_631);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = lean_st_ref_take(x_4, x_633);
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_638 = x_635;
} else {
 lean_dec_ref(x_635);
 x_638 = lean_box(0);
}
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_640 = x_636;
} else {
 lean_dec_ref(x_636);
 x_640 = lean_box(0);
}
if (lean_is_scalar(x_640)) {
 x_641 = lean_alloc_ctor(0, 2, 0);
} else {
 x_641 = x_640;
}
lean_ctor_set(x_641, 0, x_634);
lean_ctor_set(x_641, 1, x_639);
x_642 = lean_st_ref_set(x_4, x_641, x_637);
x_643 = lean_ctor_get(x_642, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_644 = x_642;
} else {
 lean_dec_ref(x_642);
 x_644 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
if (lean_is_scalar(x_638)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_638;
}
lean_ctor_set(x_645, 0, x_2);
lean_ctor_set(x_645, 1, x_29);
x_646 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_646, 0, x_645);
if (lean_is_scalar(x_644)) {
 x_647 = lean_alloc_ctor(0, 2, 0);
} else {
 x_647 = x_644;
}
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_643);
x_13 = x_647;
goto block_28;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
x_648 = lean_ctor_get(x_631, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_631, 1);
lean_inc(x_649);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_650 = x_631;
} else {
 lean_dec_ref(x_631);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_648);
lean_ctor_set(x_651, 1, x_649);
x_13 = x_651;
goto block_28;
}
}
}
}
else
{
uint8_t x_652; 
lean_dec(x_66);
lean_free_object(x_56);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_652 = !lean_is_exclusive(x_73);
if (x_652 == 0)
{
x_13 = x_73;
goto block_28;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_73, 0);
x_654 = lean_ctor_get(x_73, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_73);
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_653);
lean_ctor_set(x_655, 1, x_654);
x_13 = x_655;
goto block_28;
}
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_656 = lean_ctor_get(x_56, 0);
x_657 = lean_ctor_get(x_56, 1);
x_658 = lean_ctor_get(x_56, 2);
x_659 = lean_ctor_get(x_56, 3);
lean_inc(x_659);
lean_inc(x_658);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_56);
x_660 = lean_ctor_get(x_656, 0);
lean_inc(x_660);
lean_inc(x_660);
x_661 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1___boxed), 11, 1);
lean_closure_set(x_661, 0, x_660);
lean_inc(x_1);
x_662 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_662, 0, x_1);
lean_closure_set(x_662, 1, x_661);
x_663 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec(x_663);
x_666 = lean_ctor_get(x_664, 0);
lean_inc(x_666);
lean_dec(x_664);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_667 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_666, x_662, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_665);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; uint8_t x_683; 
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_667, 1);
lean_inc(x_669);
lean_dec(x_667);
x_670 = lean_ctor_get(x_668, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_668, 1);
lean_inc(x_671);
lean_dec(x_668);
x_672 = lean_st_ref_take(x_4, x_669);
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_676 = x_673;
} else {
 lean_dec_ref(x_673);
 x_676 = lean_box(0);
}
if (lean_is_scalar(x_676)) {
 x_677 = lean_alloc_ctor(0, 2, 0);
} else {
 x_677 = x_676;
}
lean_ctor_set(x_677, 0, x_671);
lean_ctor_set(x_677, 1, x_675);
x_678 = lean_st_ref_set(x_4, x_677, x_674);
x_679 = lean_ctor_get(x_678, 1);
lean_inc(x_679);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_680 = x_678;
} else {
 lean_dec_ref(x_678);
 x_680 = lean_box(0);
}
x_681 = lean_ctor_get(x_670, 1);
lean_inc(x_681);
lean_dec(x_670);
x_682 = lean_local_ctx_num_indices(x_681);
x_683 = lean_nat_dec_lt(x_59, x_682);
lean_dec(x_682);
if (x_683 == 0)
{
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_684; 
lean_dec(x_680);
lean_dec(x_659);
lean_dec(x_656);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_684 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_657, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_679);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
lean_dec(x_684);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_685);
lean_inc(x_660);
x_687 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_660, x_685, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_686);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_688 = lean_ctor_get(x_687, 1);
lean_inc(x_688);
lean_dec(x_687);
lean_inc(x_660);
x_689 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_689, 0, x_660);
lean_inc(x_1);
x_690 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_690, 0, x_1);
lean_closure_set(x_690, 1, x_689);
x_691 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_688);
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
lean_dec(x_691);
x_694 = lean_ctor_get(x_692, 0);
lean_inc(x_694);
lean_dec(x_692);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_695 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_694, x_690, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_693);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; uint8_t x_707; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
x_698 = lean_ctor_get(x_696, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_696, 1);
lean_inc(x_699);
lean_dec(x_696);
x_700 = lean_st_ref_take(x_4, x_697);
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec(x_700);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_704 = x_701;
} else {
 lean_dec_ref(x_701);
 x_704 = lean_box(0);
}
if (lean_is_scalar(x_704)) {
 x_705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_705 = x_704;
}
lean_ctor_set(x_705, 0, x_699);
lean_ctor_set(x_705, 1, x_703);
x_706 = lean_st_ref_set(x_4, x_705, x_702);
x_707 = lean_unbox(x_698);
lean_dec(x_698);
if (x_707 == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec(x_685);
lean_dec(x_660);
x_708 = lean_ctor_get(x_706, 1);
lean_inc(x_708);
lean_dec(x_706);
x_709 = lean_st_ref_take(x_4, x_708);
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec(x_709);
x_712 = lean_ctor_get(x_710, 0);
lean_inc(x_712);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_713 = x_710;
} else {
 lean_dec_ref(x_710);
 x_713 = lean_box(0);
}
if (lean_is_scalar(x_713)) {
 x_714 = lean_alloc_ctor(0, 2, 0);
} else {
 x_714 = x_713;
}
lean_ctor_set(x_714, 0, x_712);
lean_ctor_set(x_714, 1, x_60);
x_715 = lean_st_ref_set(x_4, x_714, x_711);
x_716 = lean_ctor_get(x_715, 1);
lean_inc(x_716);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_717 = x_715;
} else {
 lean_dec_ref(x_715);
 x_717 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_718 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_716);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_721 = x_718;
} else {
 lean_dec_ref(x_718);
 x_721 = lean_box(0);
}
x_722 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_722, 0, x_719);
if (lean_is_scalar(x_717)) {
 x_723 = lean_alloc_ctor(0, 2, 0);
} else {
 x_723 = x_717;
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_29);
x_724 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_724, 0, x_723);
if (lean_is_scalar(x_721)) {
 x_725 = lean_alloc_ctor(0, 2, 0);
} else {
 x_725 = x_721;
}
lean_ctor_set(x_725, 0, x_724);
lean_ctor_set(x_725, 1, x_720);
x_13 = x_725;
goto block_28;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_717);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_726 = lean_ctor_get(x_718, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_718, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_728 = x_718;
} else {
 lean_dec_ref(x_718);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(1, 2, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_726);
lean_ctor_set(x_729, 1, x_727);
x_13 = x_729;
goto block_28;
}
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
lean_dec(x_58);
x_730 = lean_ctor_get(x_706, 1);
lean_inc(x_730);
if (lean_is_exclusive(x_706)) {
 lean_ctor_release(x_706, 0);
 lean_ctor_release(x_706, 1);
 x_731 = x_706;
} else {
 lean_dec_ref(x_706);
 x_731 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_685);
x_732 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__4), 11, 2);
lean_closure_set(x_732, 0, x_685);
lean_closure_set(x_732, 1, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_733 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_660, x_732, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_730);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; 
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; 
lean_dec(x_60);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
lean_dec(x_733);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_685);
x_736 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_685, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_735);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_737 = lean_ctor_get(x_736, 1);
lean_inc(x_737);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_738 = x_736;
} else {
 lean_dec_ref(x_736);
 x_738 = lean_box(0);
}
lean_ctor_set(x_55, 0, x_685);
x_739 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_731)) {
 x_740 = lean_alloc_ctor(0, 2, 0);
} else {
 x_740 = x_731;
}
lean_ctor_set(x_740, 0, x_739);
lean_ctor_set(x_740, 1, x_29);
x_741 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_741, 0, x_740);
if (lean_is_scalar(x_738)) {
 x_742 = lean_alloc_ctor(0, 2, 0);
} else {
 x_742 = x_738;
}
lean_ctor_set(x_742, 0, x_741);
lean_ctor_set(x_742, 1, x_737);
x_13 = x_742;
goto block_28;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
lean_dec(x_731);
lean_dec(x_685);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_743 = lean_ctor_get(x_736, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_736, 1);
lean_inc(x_744);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_745 = x_736;
} else {
 lean_dec_ref(x_736);
 x_745 = lean_box(0);
}
if (lean_is_scalar(x_745)) {
 x_746 = lean_alloc_ctor(1, 2, 0);
} else {
 x_746 = x_745;
}
lean_ctor_set(x_746, 0, x_743);
lean_ctor_set(x_746, 1, x_744);
x_13 = x_746;
goto block_28;
}
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec(x_59);
lean_dec(x_31);
x_747 = lean_ctor_get(x_733, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_733)) {
 lean_ctor_release(x_733, 0);
 lean_ctor_release(x_733, 1);
 x_748 = x_733;
} else {
 lean_dec_ref(x_733);
 x_748 = lean_box(0);
}
x_749 = lean_ctor_get(x_734, 0);
lean_inc(x_749);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 x_750 = x_734;
} else {
 lean_dec_ref(x_734);
 x_750 = lean_box(0);
}
lean_ctor_set(x_55, 1, x_749);
lean_ctor_set(x_55, 0, x_685);
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
if (lean_is_scalar(x_731)) {
 x_751 = lean_alloc_ctor(0, 2, 0);
} else {
 x_751 = x_731;
}
lean_ctor_set(x_751, 0, x_2);
lean_ctor_set(x_751, 1, x_29);
if (lean_is_scalar(x_750)) {
 x_752 = lean_alloc_ctor(1, 1, 0);
} else {
 x_752 = x_750;
}
lean_ctor_set(x_752, 0, x_751);
if (lean_is_scalar(x_748)) {
 x_753 = lean_alloc_ctor(0, 2, 0);
} else {
 x_753 = x_748;
}
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_747);
x_13 = x_753;
goto block_28;
}
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
lean_dec(x_731);
lean_dec(x_685);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_free_object(x_29);
lean_dec(x_31);
x_754 = lean_ctor_get(x_733, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_733, 1);
lean_inc(x_755);
if (lean_is_exclusive(x_733)) {
 lean_ctor_release(x_733, 0);
 lean_ctor_release(x_733, 1);
 x_756 = x_733;
} else {
 lean_dec_ref(x_733);
 x_756 = lean_box(0);
}
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(1, 2, 0);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_754);
lean_ctor_set(x_757, 1, x_755);
x_13 = x_757;
goto block_28;
}
}
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
lean_dec(x_685);
lean_dec(x_660);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_758 = lean_ctor_get(x_695, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_695, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_695)) {
 lean_ctor_release(x_695, 0);
 lean_ctor_release(x_695, 1);
 x_760 = x_695;
} else {
 lean_dec_ref(x_695);
 x_760 = lean_box(0);
}
if (lean_is_scalar(x_760)) {
 x_761 = lean_alloc_ctor(1, 2, 0);
} else {
 x_761 = x_760;
}
lean_ctor_set(x_761, 0, x_758);
lean_ctor_set(x_761, 1, x_759);
x_13 = x_761;
goto block_28;
}
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_685);
lean_dec(x_660);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_762 = lean_ctor_get(x_687, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_687, 1);
lean_inc(x_763);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_764 = x_687;
} else {
 lean_dec_ref(x_687);
 x_764 = lean_box(0);
}
if (lean_is_scalar(x_764)) {
 x_765 = lean_alloc_ctor(1, 2, 0);
} else {
 x_765 = x_764;
}
lean_ctor_set(x_765, 0, x_762);
lean_ctor_set(x_765, 1, x_763);
x_13 = x_765;
goto block_28;
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_660);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_766 = lean_ctor_get(x_684, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_684, 1);
lean_inc(x_767);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_768 = x_684;
} else {
 lean_dec_ref(x_684);
 x_768 = lean_box(0);
}
if (lean_is_scalar(x_768)) {
 x_769 = lean_alloc_ctor(1, 2, 0);
} else {
 x_769 = x_768;
}
lean_ctor_set(x_769, 0, x_766);
lean_ctor_set(x_769, 1, x_767);
x_13 = x_769;
goto block_28;
}
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
lean_dec(x_660);
x_770 = lean_ctor_get(x_658, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_658, 1);
lean_inc(x_771);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_772 = x_658;
} else {
 lean_dec_ref(x_658);
 x_772 = lean_box(0);
}
lean_inc(x_659);
x_773 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_773, 0, x_656);
lean_ctor_set(x_773, 1, x_657);
lean_ctor_set(x_773, 2, x_771);
lean_ctor_set(x_773, 3, x_659);
x_774 = lean_st_ref_take(x_4, x_679);
x_775 = lean_ctor_get(x_774, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_776 = x_774;
} else {
 lean_dec_ref(x_774);
 x_776 = lean_box(0);
}
if (lean_is_scalar(x_772)) {
 x_777 = lean_alloc_ctor(1, 2, 0);
} else {
 x_777 = x_772;
}
lean_ctor_set(x_777, 0, x_773);
lean_ctor_set(x_777, 1, x_60);
if (lean_is_scalar(x_776)) {
 x_778 = lean_alloc_ctor(0, 2, 0);
} else {
 x_778 = x_776;
}
lean_ctor_set(x_778, 0, x_770);
lean_ctor_set(x_778, 1, x_777);
x_779 = lean_st_ref_set(x_4, x_778, x_775);
x_780 = lean_ctor_get(x_779, 1);
lean_inc(x_780);
if (lean_is_exclusive(x_779)) {
 lean_ctor_release(x_779, 0);
 lean_ctor_release(x_779, 1);
 x_781 = x_779;
} else {
 lean_dec_ref(x_779);
 x_781 = lean_box(0);
}
x_782 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_782, 0, x_659);
x_783 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_783, 0, x_782);
if (lean_is_scalar(x_680)) {
 x_784 = lean_alloc_ctor(0, 2, 0);
} else {
 x_784 = x_680;
}
lean_ctor_set(x_784, 0, x_783);
lean_ctor_set(x_784, 1, x_29);
x_785 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_785, 0, x_784);
if (lean_is_scalar(x_781)) {
 x_786 = lean_alloc_ctor(0, 2, 0);
} else {
 x_786 = x_781;
}
lean_ctor_set(x_786, 0, x_785);
lean_ctor_set(x_786, 1, x_780);
x_13 = x_786;
goto block_28;
}
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
lean_dec(x_680);
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_31);
lean_inc(x_58);
x_787 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_787, 0, x_660);
lean_closure_set(x_787, 1, x_58);
lean_inc(x_1);
x_788 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_788, 0, x_1);
lean_closure_set(x_788, 1, x_787);
x_789 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_679);
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
x_792 = lean_ctor_get(x_790, 0);
lean_inc(x_792);
lean_dec(x_790);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_793 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_792, x_788, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_791);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
x_796 = lean_ctor_get(x_794, 1);
lean_inc(x_796);
lean_dec(x_794);
x_797 = lean_st_ref_take(x_4, x_795);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 x_800 = x_797;
} else {
 lean_dec_ref(x_797);
 x_800 = lean_box(0);
}
x_801 = lean_ctor_get(x_798, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 x_802 = x_798;
} else {
 lean_dec_ref(x_798);
 x_802 = lean_box(0);
}
if (lean_is_scalar(x_802)) {
 x_803 = lean_alloc_ctor(0, 2, 0);
} else {
 x_803 = x_802;
}
lean_ctor_set(x_803, 0, x_796);
lean_ctor_set(x_803, 1, x_801);
x_804 = lean_st_ref_set(x_4, x_803, x_799);
x_805 = lean_ctor_get(x_804, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_804)) {
 lean_ctor_release(x_804, 0);
 lean_ctor_release(x_804, 1);
 x_806 = x_804;
} else {
 lean_dec_ref(x_804);
 x_806 = lean_box(0);
}
lean_ctor_set(x_29, 0, x_60);
lean_inc(x_2);
if (lean_is_scalar(x_800)) {
 x_807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_807 = x_800;
}
lean_ctor_set(x_807, 0, x_2);
lean_ctor_set(x_807, 1, x_29);
x_808 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_808, 0, x_807);
if (lean_is_scalar(x_806)) {
 x_809 = lean_alloc_ctor(0, 2, 0);
} else {
 x_809 = x_806;
}
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_805);
x_13 = x_809;
goto block_28;
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
x_810 = lean_ctor_get(x_793, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_793, 1);
lean_inc(x_811);
if (lean_is_exclusive(x_793)) {
 lean_ctor_release(x_793, 0);
 lean_ctor_release(x_793, 1);
 x_812 = x_793;
} else {
 lean_dec_ref(x_793);
 x_812 = lean_box(0);
}
if (lean_is_scalar(x_812)) {
 x_813 = lean_alloc_ctor(1, 2, 0);
} else {
 x_813 = x_812;
}
lean_ctor_set(x_813, 0, x_810);
lean_ctor_set(x_813, 1, x_811);
x_13 = x_813;
goto block_28;
}
}
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
lean_dec(x_660);
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_60);
lean_free_object(x_55);
lean_dec(x_59);
lean_dec(x_58);
lean_free_object(x_29);
lean_dec(x_31);
x_814 = lean_ctor_get(x_667, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_667, 1);
lean_inc(x_815);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_816 = x_667;
} else {
 lean_dec_ref(x_667);
 x_816 = lean_box(0);
}
if (lean_is_scalar(x_816)) {
 x_817 = lean_alloc_ctor(1, 2, 0);
} else {
 x_817 = x_816;
}
lean_ctor_set(x_817, 0, x_814);
lean_ctor_set(x_817, 1, x_815);
x_13 = x_817;
goto block_28;
}
}
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_818 = lean_ctor_get(x_55, 0);
x_819 = lean_ctor_get(x_55, 1);
lean_inc(x_819);
lean_inc(x_818);
lean_dec(x_55);
x_820 = lean_ctor_get(x_31, 1);
lean_inc(x_820);
x_821 = lean_ctor_get(x_56, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_56, 1);
lean_inc(x_822);
x_823 = lean_ctor_get(x_56, 2);
lean_inc(x_823);
x_824 = lean_ctor_get(x_56, 3);
lean_inc(x_824);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 x_825 = x_56;
} else {
 lean_dec_ref(x_56);
 x_825 = lean_box(0);
}
x_826 = lean_ctor_get(x_821, 0);
lean_inc(x_826);
lean_inc(x_826);
x_827 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1___boxed), 11, 1);
lean_closure_set(x_827, 0, x_826);
lean_inc(x_1);
x_828 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_828, 0, x_1);
lean_closure_set(x_828, 1, x_827);
x_829 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
lean_dec(x_829);
x_832 = lean_ctor_get(x_830, 0);
lean_inc(x_832);
lean_dec(x_830);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_833 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_832, x_828, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_831);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; uint8_t x_849; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
lean_dec(x_833);
x_836 = lean_ctor_get(x_834, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_834, 1);
lean_inc(x_837);
lean_dec(x_834);
x_838 = lean_st_ref_take(x_4, x_835);
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_838, 1);
lean_inc(x_840);
lean_dec(x_838);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
if (lean_is_exclusive(x_839)) {
 lean_ctor_release(x_839, 0);
 lean_ctor_release(x_839, 1);
 x_842 = x_839;
} else {
 lean_dec_ref(x_839);
 x_842 = lean_box(0);
}
if (lean_is_scalar(x_842)) {
 x_843 = lean_alloc_ctor(0, 2, 0);
} else {
 x_843 = x_842;
}
lean_ctor_set(x_843, 0, x_837);
lean_ctor_set(x_843, 1, x_841);
x_844 = lean_st_ref_set(x_4, x_843, x_840);
x_845 = lean_ctor_get(x_844, 1);
lean_inc(x_845);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_846 = x_844;
} else {
 lean_dec_ref(x_844);
 x_846 = lean_box(0);
}
x_847 = lean_ctor_get(x_836, 1);
lean_inc(x_847);
lean_dec(x_836);
x_848 = lean_local_ctx_num_indices(x_847);
x_849 = lean_nat_dec_lt(x_819, x_848);
lean_dec(x_848);
if (x_849 == 0)
{
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_850; 
lean_dec(x_846);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_821);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_850 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_822, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_845);
if (lean_obj_tag(x_850) == 0)
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_851 = lean_ctor_get(x_850, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_850, 1);
lean_inc(x_852);
lean_dec(x_850);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_851);
lean_inc(x_826);
x_853 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_826, x_851, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_852);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_854 = lean_ctor_get(x_853, 1);
lean_inc(x_854);
lean_dec(x_853);
lean_inc(x_826);
x_855 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_855, 0, x_826);
lean_inc(x_1);
x_856 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_856, 0, x_1);
lean_closure_set(x_856, 1, x_855);
x_857 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_854);
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
lean_dec(x_857);
x_860 = lean_ctor_get(x_858, 0);
lean_inc(x_860);
lean_dec(x_858);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_861 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_860, x_856, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_859);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; uint8_t x_873; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
x_864 = lean_ctor_get(x_862, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_862, 1);
lean_inc(x_865);
lean_dec(x_862);
x_866 = lean_st_ref_take(x_4, x_863);
x_867 = lean_ctor_get(x_866, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_866, 1);
lean_inc(x_868);
lean_dec(x_866);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 lean_ctor_release(x_867, 1);
 x_870 = x_867;
} else {
 lean_dec_ref(x_867);
 x_870 = lean_box(0);
}
if (lean_is_scalar(x_870)) {
 x_871 = lean_alloc_ctor(0, 2, 0);
} else {
 x_871 = x_870;
}
lean_ctor_set(x_871, 0, x_865);
lean_ctor_set(x_871, 1, x_869);
x_872 = lean_st_ref_set(x_4, x_871, x_868);
x_873 = lean_unbox(x_864);
lean_dec(x_864);
if (x_873 == 0)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec(x_851);
lean_dec(x_826);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_875 = lean_st_ref_take(x_4, x_874);
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
x_878 = lean_ctor_get(x_876, 0);
lean_inc(x_878);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 lean_ctor_release(x_876, 1);
 x_879 = x_876;
} else {
 lean_dec_ref(x_876);
 x_879 = lean_box(0);
}
if (lean_is_scalar(x_879)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_879;
}
lean_ctor_set(x_880, 0, x_878);
lean_ctor_set(x_880, 1, x_820);
x_881 = lean_st_ref_set(x_4, x_880, x_877);
x_882 = lean_ctor_get(x_881, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_881)) {
 lean_ctor_release(x_881, 0);
 lean_ctor_release(x_881, 1);
 x_883 = x_881;
} else {
 lean_dec_ref(x_881);
 x_883 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_884 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_882);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 lean_ctor_release(x_884, 1);
 x_887 = x_884;
} else {
 lean_dec_ref(x_884);
 x_887 = lean_box(0);
}
x_888 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_888, 0, x_885);
x_889 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_889, 0, x_818);
lean_ctor_set(x_889, 1, x_819);
lean_ctor_set(x_29, 1, x_889);
if (lean_is_scalar(x_883)) {
 x_890 = lean_alloc_ctor(0, 2, 0);
} else {
 x_890 = x_883;
}
lean_ctor_set(x_890, 0, x_888);
lean_ctor_set(x_890, 1, x_29);
x_891 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_891, 0, x_890);
if (lean_is_scalar(x_887)) {
 x_892 = lean_alloc_ctor(0, 2, 0);
} else {
 x_892 = x_887;
}
lean_ctor_set(x_892, 0, x_891);
lean_ctor_set(x_892, 1, x_886);
x_13 = x_892;
goto block_28;
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
lean_dec(x_883);
lean_dec(x_819);
lean_dec(x_818);
lean_free_object(x_29);
lean_dec(x_31);
x_893 = lean_ctor_get(x_884, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_884, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 lean_ctor_release(x_884, 1);
 x_895 = x_884;
} else {
 lean_dec_ref(x_884);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_895)) {
 x_896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_896 = x_895;
}
lean_ctor_set(x_896, 0, x_893);
lean_ctor_set(x_896, 1, x_894);
x_13 = x_896;
goto block_28;
}
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
lean_dec(x_818);
x_897 = lean_ctor_get(x_872, 1);
lean_inc(x_897);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_898 = x_872;
} else {
 lean_dec_ref(x_872);
 x_898 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_851);
x_899 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__4), 11, 2);
lean_closure_set(x_899, 0, x_851);
lean_closure_set(x_899, 1, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_900 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_826, x_899, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_897);
if (lean_obj_tag(x_900) == 0)
{
lean_object* x_901; 
x_901 = lean_ctor_get(x_900, 0);
lean_inc(x_901);
if (lean_obj_tag(x_901) == 0)
{
lean_object* x_902; lean_object* x_903; 
lean_dec(x_820);
x_902 = lean_ctor_get(x_900, 1);
lean_inc(x_902);
lean_dec(x_900);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_851);
x_903 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_851, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_902);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_904 = lean_ctor_get(x_903, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 lean_ctor_release(x_903, 1);
 x_905 = x_903;
} else {
 lean_dec_ref(x_903);
 x_905 = lean_box(0);
}
x_906 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_906, 0, x_851);
lean_ctor_set(x_906, 1, x_819);
lean_ctor_set(x_29, 1, x_906);
x_907 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_898)) {
 x_908 = lean_alloc_ctor(0, 2, 0);
} else {
 x_908 = x_898;
}
lean_ctor_set(x_908, 0, x_907);
lean_ctor_set(x_908, 1, x_29);
x_909 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_909, 0, x_908);
if (lean_is_scalar(x_905)) {
 x_910 = lean_alloc_ctor(0, 2, 0);
} else {
 x_910 = x_905;
}
lean_ctor_set(x_910, 0, x_909);
lean_ctor_set(x_910, 1, x_904);
x_13 = x_910;
goto block_28;
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
lean_dec(x_898);
lean_dec(x_851);
lean_dec(x_819);
lean_free_object(x_29);
lean_dec(x_31);
x_911 = lean_ctor_get(x_903, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_903, 1);
lean_inc(x_912);
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 lean_ctor_release(x_903, 1);
 x_913 = x_903;
} else {
 lean_dec_ref(x_903);
 x_913 = lean_box(0);
}
if (lean_is_scalar(x_913)) {
 x_914 = lean_alloc_ctor(1, 2, 0);
} else {
 x_914 = x_913;
}
lean_ctor_set(x_914, 0, x_911);
lean_ctor_set(x_914, 1, x_912);
x_13 = x_914;
goto block_28;
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
lean_dec(x_819);
lean_dec(x_31);
x_915 = lean_ctor_get(x_900, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_900)) {
 lean_ctor_release(x_900, 0);
 lean_ctor_release(x_900, 1);
 x_916 = x_900;
} else {
 lean_dec_ref(x_900);
 x_916 = lean_box(0);
}
x_917 = lean_ctor_get(x_901, 0);
lean_inc(x_917);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 x_918 = x_901;
} else {
 lean_dec_ref(x_901);
 x_918 = lean_box(0);
}
x_919 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_919, 0, x_851);
lean_ctor_set(x_919, 1, x_917);
lean_ctor_set(x_29, 1, x_919);
lean_ctor_set(x_29, 0, x_820);
lean_inc(x_2);
if (lean_is_scalar(x_898)) {
 x_920 = lean_alloc_ctor(0, 2, 0);
} else {
 x_920 = x_898;
}
lean_ctor_set(x_920, 0, x_2);
lean_ctor_set(x_920, 1, x_29);
if (lean_is_scalar(x_918)) {
 x_921 = lean_alloc_ctor(1, 1, 0);
} else {
 x_921 = x_918;
}
lean_ctor_set(x_921, 0, x_920);
if (lean_is_scalar(x_916)) {
 x_922 = lean_alloc_ctor(0, 2, 0);
} else {
 x_922 = x_916;
}
lean_ctor_set(x_922, 0, x_921);
lean_ctor_set(x_922, 1, x_915);
x_13 = x_922;
goto block_28;
}
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
lean_dec(x_898);
lean_dec(x_851);
lean_dec(x_820);
lean_dec(x_819);
lean_free_object(x_29);
lean_dec(x_31);
x_923 = lean_ctor_get(x_900, 0);
lean_inc(x_923);
x_924 = lean_ctor_get(x_900, 1);
lean_inc(x_924);
if (lean_is_exclusive(x_900)) {
 lean_ctor_release(x_900, 0);
 lean_ctor_release(x_900, 1);
 x_925 = x_900;
} else {
 lean_dec_ref(x_900);
 x_925 = lean_box(0);
}
if (lean_is_scalar(x_925)) {
 x_926 = lean_alloc_ctor(1, 2, 0);
} else {
 x_926 = x_925;
}
lean_ctor_set(x_926, 0, x_923);
lean_ctor_set(x_926, 1, x_924);
x_13 = x_926;
goto block_28;
}
}
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
lean_dec(x_851);
lean_dec(x_826);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_free_object(x_29);
lean_dec(x_31);
x_927 = lean_ctor_get(x_861, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_861, 1);
lean_inc(x_928);
if (lean_is_exclusive(x_861)) {
 lean_ctor_release(x_861, 0);
 lean_ctor_release(x_861, 1);
 x_929 = x_861;
} else {
 lean_dec_ref(x_861);
 x_929 = lean_box(0);
}
if (lean_is_scalar(x_929)) {
 x_930 = lean_alloc_ctor(1, 2, 0);
} else {
 x_930 = x_929;
}
lean_ctor_set(x_930, 0, x_927);
lean_ctor_set(x_930, 1, x_928);
x_13 = x_930;
goto block_28;
}
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_851);
lean_dec(x_826);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_free_object(x_29);
lean_dec(x_31);
x_931 = lean_ctor_get(x_853, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_853, 1);
lean_inc(x_932);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_933 = x_853;
} else {
 lean_dec_ref(x_853);
 x_933 = lean_box(0);
}
if (lean_is_scalar(x_933)) {
 x_934 = lean_alloc_ctor(1, 2, 0);
} else {
 x_934 = x_933;
}
lean_ctor_set(x_934, 0, x_931);
lean_ctor_set(x_934, 1, x_932);
x_13 = x_934;
goto block_28;
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_826);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_free_object(x_29);
lean_dec(x_31);
x_935 = lean_ctor_get(x_850, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_850, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_850)) {
 lean_ctor_release(x_850, 0);
 lean_ctor_release(x_850, 1);
 x_937 = x_850;
} else {
 lean_dec_ref(x_850);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(1, 2, 0);
} else {
 x_938 = x_937;
}
lean_ctor_set(x_938, 0, x_935);
lean_ctor_set(x_938, 1, x_936);
x_13 = x_938;
goto block_28;
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
lean_dec(x_826);
x_939 = lean_ctor_get(x_823, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_823, 1);
lean_inc(x_940);
if (lean_is_exclusive(x_823)) {
 lean_ctor_release(x_823, 0);
 lean_ctor_release(x_823, 1);
 x_941 = x_823;
} else {
 lean_dec_ref(x_823);
 x_941 = lean_box(0);
}
lean_inc(x_824);
if (lean_is_scalar(x_825)) {
 x_942 = lean_alloc_ctor(0, 4, 0);
} else {
 x_942 = x_825;
}
lean_ctor_set(x_942, 0, x_821);
lean_ctor_set(x_942, 1, x_822);
lean_ctor_set(x_942, 2, x_940);
lean_ctor_set(x_942, 3, x_824);
x_943 = lean_st_ref_take(x_4, x_845);
x_944 = lean_ctor_get(x_943, 1);
lean_inc(x_944);
if (lean_is_exclusive(x_943)) {
 lean_ctor_release(x_943, 0);
 lean_ctor_release(x_943, 1);
 x_945 = x_943;
} else {
 lean_dec_ref(x_943);
 x_945 = lean_box(0);
}
if (lean_is_scalar(x_941)) {
 x_946 = lean_alloc_ctor(1, 2, 0);
} else {
 x_946 = x_941;
}
lean_ctor_set(x_946, 0, x_942);
lean_ctor_set(x_946, 1, x_820);
if (lean_is_scalar(x_945)) {
 x_947 = lean_alloc_ctor(0, 2, 0);
} else {
 x_947 = x_945;
}
lean_ctor_set(x_947, 0, x_939);
lean_ctor_set(x_947, 1, x_946);
x_948 = lean_st_ref_set(x_4, x_947, x_944);
x_949 = lean_ctor_get(x_948, 1);
lean_inc(x_949);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_950 = x_948;
} else {
 lean_dec_ref(x_948);
 x_950 = lean_box(0);
}
x_951 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_951, 0, x_824);
x_952 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_952, 0, x_951);
x_953 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_953, 0, x_818);
lean_ctor_set(x_953, 1, x_819);
lean_ctor_set(x_29, 1, x_953);
if (lean_is_scalar(x_846)) {
 x_954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_954 = x_846;
}
lean_ctor_set(x_954, 0, x_952);
lean_ctor_set(x_954, 1, x_29);
x_955 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_955, 0, x_954);
if (lean_is_scalar(x_950)) {
 x_956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_956 = x_950;
}
lean_ctor_set(x_956, 0, x_955);
lean_ctor_set(x_956, 1, x_949);
x_13 = x_956;
goto block_28;
}
}
else
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; 
lean_dec(x_846);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_31);
lean_inc(x_818);
x_957 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_957, 0, x_826);
lean_closure_set(x_957, 1, x_818);
lean_inc(x_1);
x_958 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_958, 0, x_1);
lean_closure_set(x_958, 1, x_957);
x_959 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_845);
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
x_961 = lean_ctor_get(x_959, 1);
lean_inc(x_961);
lean_dec(x_959);
x_962 = lean_ctor_get(x_960, 0);
lean_inc(x_962);
lean_dec(x_960);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_963 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_962, x_958, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_961);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_963, 1);
lean_inc(x_965);
lean_dec(x_963);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
lean_dec(x_964);
x_967 = lean_st_ref_take(x_4, x_965);
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_967, 1);
lean_inc(x_969);
if (lean_is_exclusive(x_967)) {
 lean_ctor_release(x_967, 0);
 lean_ctor_release(x_967, 1);
 x_970 = x_967;
} else {
 lean_dec_ref(x_967);
 x_970 = lean_box(0);
}
x_971 = lean_ctor_get(x_968, 1);
lean_inc(x_971);
if (lean_is_exclusive(x_968)) {
 lean_ctor_release(x_968, 0);
 lean_ctor_release(x_968, 1);
 x_972 = x_968;
} else {
 lean_dec_ref(x_968);
 x_972 = lean_box(0);
}
if (lean_is_scalar(x_972)) {
 x_973 = lean_alloc_ctor(0, 2, 0);
} else {
 x_973 = x_972;
}
lean_ctor_set(x_973, 0, x_966);
lean_ctor_set(x_973, 1, x_971);
x_974 = lean_st_ref_set(x_4, x_973, x_969);
x_975 = lean_ctor_get(x_974, 1);
lean_inc(x_975);
if (lean_is_exclusive(x_974)) {
 lean_ctor_release(x_974, 0);
 lean_ctor_release(x_974, 1);
 x_976 = x_974;
} else {
 lean_dec_ref(x_974);
 x_976 = lean_box(0);
}
x_977 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_977, 0, x_818);
lean_ctor_set(x_977, 1, x_819);
lean_ctor_set(x_29, 1, x_977);
lean_ctor_set(x_29, 0, x_820);
lean_inc(x_2);
if (lean_is_scalar(x_970)) {
 x_978 = lean_alloc_ctor(0, 2, 0);
} else {
 x_978 = x_970;
}
lean_ctor_set(x_978, 0, x_2);
lean_ctor_set(x_978, 1, x_29);
x_979 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_979, 0, x_978);
if (lean_is_scalar(x_976)) {
 x_980 = lean_alloc_ctor(0, 2, 0);
} else {
 x_980 = x_976;
}
lean_ctor_set(x_980, 0, x_979);
lean_ctor_set(x_980, 1, x_975);
x_13 = x_980;
goto block_28;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_free_object(x_29);
x_981 = lean_ctor_get(x_963, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_963, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 lean_ctor_release(x_963, 1);
 x_983 = x_963;
} else {
 lean_dec_ref(x_963);
 x_983 = lean_box(0);
}
if (lean_is_scalar(x_983)) {
 x_984 = lean_alloc_ctor(1, 2, 0);
} else {
 x_984 = x_983;
}
lean_ctor_set(x_984, 0, x_981);
lean_ctor_set(x_984, 1, x_982);
x_13 = x_984;
goto block_28;
}
}
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_free_object(x_29);
lean_dec(x_31);
x_985 = lean_ctor_get(x_833, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_833, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_987 = x_833;
} else {
 lean_dec_ref(x_833);
 x_987 = lean_box(0);
}
if (lean_is_scalar(x_987)) {
 x_988 = lean_alloc_ctor(1, 2, 0);
} else {
 x_988 = x_987;
}
lean_ctor_set(x_988, 0, x_985);
lean_ctor_set(x_988, 1, x_986);
x_13 = x_988;
goto block_28;
}
}
}
}
else
{
lean_object* x_989; lean_object* x_990; 
x_989 = lean_ctor_get(x_29, 1);
x_990 = lean_ctor_get(x_29, 0);
lean_inc(x_989);
lean_inc(x_990);
lean_dec(x_29);
if (lean_obj_tag(x_990) == 0)
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_991 = lean_ctor_get(x_989, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_989, 1);
lean_inc(x_992);
if (lean_is_exclusive(x_989)) {
 lean_ctor_release(x_989, 0);
 lean_ctor_release(x_989, 1);
 x_993 = x_989;
} else {
 lean_dec_ref(x_989);
 x_993 = lean_box(0);
}
x_994 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_995 = lean_ctor_get(x_994, 1);
lean_inc(x_995);
if (lean_is_exclusive(x_994)) {
 lean_ctor_release(x_994, 0);
 lean_ctor_release(x_994, 1);
 x_996 = x_994;
} else {
 lean_dec_ref(x_994);
 x_996 = lean_box(0);
}
if (lean_is_scalar(x_993)) {
 x_997 = lean_alloc_ctor(0, 2, 0);
} else {
 x_997 = x_993;
}
lean_ctor_set(x_997, 0, x_991);
lean_ctor_set(x_997, 1, x_992);
x_998 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_998, 0, x_990);
lean_ctor_set(x_998, 1, x_997);
x_999 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_1000 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1000, 0, x_999);
lean_ctor_set(x_1000, 1, x_998);
x_1001 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1001, 0, x_1000);
if (lean_is_scalar(x_996)) {
 x_1002 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1002 = x_996;
}
lean_ctor_set(x_1002, 0, x_1001);
lean_ctor_set(x_1002, 1, x_995);
x_13 = x_1002;
goto block_28;
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1003 = lean_ctor_get(x_990, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_989, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_989, 1);
lean_inc(x_1005);
if (lean_is_exclusive(x_989)) {
 lean_ctor_release(x_989, 0);
 lean_ctor_release(x_989, 1);
 x_1006 = x_989;
} else {
 lean_dec_ref(x_989);
 x_1006 = lean_box(0);
}
x_1007 = lean_ctor_get(x_990, 1);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1003, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_1003, 1);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_1003, 2);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_1003, 3);
lean_inc(x_1011);
if (lean_is_exclusive(x_1003)) {
 lean_ctor_release(x_1003, 0);
 lean_ctor_release(x_1003, 1);
 lean_ctor_release(x_1003, 2);
 lean_ctor_release(x_1003, 3);
 x_1012 = x_1003;
} else {
 lean_dec_ref(x_1003);
 x_1012 = lean_box(0);
}
x_1013 = lean_ctor_get(x_1008, 0);
lean_inc(x_1013);
lean_inc(x_1013);
x_1014 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1___boxed), 11, 1);
lean_closure_set(x_1014, 0, x_1013);
lean_inc(x_1);
x_1015 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_1015, 0, x_1);
lean_closure_set(x_1015, 1, x_1014);
x_1016 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1016, 1);
lean_inc(x_1018);
lean_dec(x_1016);
x_1019 = lean_ctor_get(x_1017, 0);
lean_inc(x_1019);
lean_dec(x_1017);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1020 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_1019, x_1015, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_1018);
if (lean_obj_tag(x_1020) == 0)
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; uint8_t x_1036; 
x_1021 = lean_ctor_get(x_1020, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1020, 1);
lean_inc(x_1022);
lean_dec(x_1020);
x_1023 = lean_ctor_get(x_1021, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1021, 1);
lean_inc(x_1024);
lean_dec(x_1021);
x_1025 = lean_st_ref_take(x_4, x_1022);
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1025, 1);
lean_inc(x_1027);
lean_dec(x_1025);
x_1028 = lean_ctor_get(x_1026, 1);
lean_inc(x_1028);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 lean_ctor_release(x_1026, 1);
 x_1029 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1029 = lean_box(0);
}
if (lean_is_scalar(x_1029)) {
 x_1030 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1030 = x_1029;
}
lean_ctor_set(x_1030, 0, x_1024);
lean_ctor_set(x_1030, 1, x_1028);
x_1031 = lean_st_ref_set(x_4, x_1030, x_1027);
x_1032 = lean_ctor_get(x_1031, 1);
lean_inc(x_1032);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1033 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1033 = lean_box(0);
}
x_1034 = lean_ctor_get(x_1023, 1);
lean_inc(x_1034);
lean_dec(x_1023);
x_1035 = lean_local_ctx_num_indices(x_1034);
x_1036 = lean_nat_dec_lt(x_1005, x_1035);
lean_dec(x_1035);
if (x_1036 == 0)
{
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1037; 
lean_dec(x_1033);
lean_dec(x_1012);
lean_dec(x_1011);
lean_dec(x_1008);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1037 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_1009, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_1032);
if (lean_obj_tag(x_1037) == 0)
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1038 = lean_ctor_get(x_1037, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1037, 1);
lean_inc(x_1039);
lean_dec(x_1037);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1038);
lean_inc(x_1013);
x_1040 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_1013, x_1038, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_1039);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
x_1041 = lean_ctor_get(x_1040, 1);
lean_inc(x_1041);
lean_dec(x_1040);
lean_inc(x_1013);
x_1042 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_1042, 0, x_1013);
lean_inc(x_1);
x_1043 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_1043, 0, x_1);
lean_closure_set(x_1043, 1, x_1042);
x_1044 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_1041);
x_1045 = lean_ctor_get(x_1044, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1044, 1);
lean_inc(x_1046);
lean_dec(x_1044);
x_1047 = lean_ctor_get(x_1045, 0);
lean_inc(x_1047);
lean_dec(x_1045);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1048 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_1047, x_1043, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_1046);
if (lean_obj_tag(x_1048) == 0)
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; uint8_t x_1060; 
x_1049 = lean_ctor_get(x_1048, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1048, 1);
lean_inc(x_1050);
lean_dec(x_1048);
x_1051 = lean_ctor_get(x_1049, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1049, 1);
lean_inc(x_1052);
lean_dec(x_1049);
x_1053 = lean_st_ref_take(x_4, x_1050);
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1053, 1);
lean_inc(x_1055);
lean_dec(x_1053);
x_1056 = lean_ctor_get(x_1054, 1);
lean_inc(x_1056);
if (lean_is_exclusive(x_1054)) {
 lean_ctor_release(x_1054, 0);
 lean_ctor_release(x_1054, 1);
 x_1057 = x_1054;
} else {
 lean_dec_ref(x_1054);
 x_1057 = lean_box(0);
}
if (lean_is_scalar(x_1057)) {
 x_1058 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1058 = x_1057;
}
lean_ctor_set(x_1058, 0, x_1052);
lean_ctor_set(x_1058, 1, x_1056);
x_1059 = lean_st_ref_set(x_4, x_1058, x_1055);
x_1060 = lean_unbox(x_1051);
lean_dec(x_1051);
if (x_1060 == 0)
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_1038);
lean_dec(x_1013);
x_1061 = lean_ctor_get(x_1059, 1);
lean_inc(x_1061);
lean_dec(x_1059);
x_1062 = lean_st_ref_take(x_4, x_1061);
x_1063 = lean_ctor_get(x_1062, 0);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1062, 1);
lean_inc(x_1064);
lean_dec(x_1062);
x_1065 = lean_ctor_get(x_1063, 0);
lean_inc(x_1065);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 lean_ctor_release(x_1063, 1);
 x_1066 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1066 = lean_box(0);
}
if (lean_is_scalar(x_1066)) {
 x_1067 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1067 = x_1066;
}
lean_ctor_set(x_1067, 0, x_1065);
lean_ctor_set(x_1067, 1, x_1007);
x_1068 = lean_st_ref_set(x_4, x_1067, x_1064);
x_1069 = lean_ctor_get(x_1068, 1);
lean_inc(x_1069);
if (lean_is_exclusive(x_1068)) {
 lean_ctor_release(x_1068, 0);
 lean_ctor_release(x_1068, 1);
 x_1070 = x_1068;
} else {
 lean_dec_ref(x_1068);
 x_1070 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1071 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_1069);
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1071, 1);
lean_inc(x_1073);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 x_1074 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1074 = lean_box(0);
}
x_1075 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1075, 0, x_1072);
if (lean_is_scalar(x_1006)) {
 x_1076 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1076 = x_1006;
}
lean_ctor_set(x_1076, 0, x_1004);
lean_ctor_set(x_1076, 1, x_1005);
x_1077 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1077, 0, x_990);
lean_ctor_set(x_1077, 1, x_1076);
if (lean_is_scalar(x_1070)) {
 x_1078 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1078 = x_1070;
}
lean_ctor_set(x_1078, 0, x_1075);
lean_ctor_set(x_1078, 1, x_1077);
x_1079 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1079, 0, x_1078);
if (lean_is_scalar(x_1074)) {
 x_1080 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1080 = x_1074;
}
lean_ctor_set(x_1080, 0, x_1079);
lean_ctor_set(x_1080, 1, x_1073);
x_13 = x_1080;
goto block_28;
}
else
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
lean_dec(x_1070);
lean_dec(x_1006);
lean_dec(x_1005);
lean_dec(x_1004);
lean_dec(x_990);
x_1081 = lean_ctor_get(x_1071, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1071, 1);
lean_inc(x_1082);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 x_1083 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1083 = lean_box(0);
}
if (lean_is_scalar(x_1083)) {
 x_1084 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1084 = x_1083;
}
lean_ctor_set(x_1084, 0, x_1081);
lean_ctor_set(x_1084, 1, x_1082);
x_13 = x_1084;
goto block_28;
}
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
lean_dec(x_1004);
x_1085 = lean_ctor_get(x_1059, 1);
lean_inc(x_1085);
if (lean_is_exclusive(x_1059)) {
 lean_ctor_release(x_1059, 0);
 lean_ctor_release(x_1059, 1);
 x_1086 = x_1059;
} else {
 lean_dec_ref(x_1059);
 x_1086 = lean_box(0);
}
lean_inc(x_1);
lean_inc(x_1038);
x_1087 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__4), 11, 2);
lean_closure_set(x_1087, 0, x_1038);
lean_closure_set(x_1087, 1, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1088 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_1013, x_1087, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_1085);
if (lean_obj_tag(x_1088) == 0)
{
lean_object* x_1089; 
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
if (lean_obj_tag(x_1089) == 0)
{
lean_object* x_1090; lean_object* x_1091; 
lean_dec(x_1007);
x_1090 = lean_ctor_get(x_1088, 1);
lean_inc(x_1090);
lean_dec(x_1088);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1038);
x_1091 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_1038, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_1090);
if (lean_obj_tag(x_1091) == 0)
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1092 = lean_ctor_get(x_1091, 1);
lean_inc(x_1092);
if (lean_is_exclusive(x_1091)) {
 lean_ctor_release(x_1091, 0);
 lean_ctor_release(x_1091, 1);
 x_1093 = x_1091;
} else {
 lean_dec_ref(x_1091);
 x_1093 = lean_box(0);
}
if (lean_is_scalar(x_1006)) {
 x_1094 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1094 = x_1006;
}
lean_ctor_set(x_1094, 0, x_1038);
lean_ctor_set(x_1094, 1, x_1005);
x_1095 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1095, 0, x_990);
lean_ctor_set(x_1095, 1, x_1094);
x_1096 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_1086)) {
 x_1097 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1097 = x_1086;
}
lean_ctor_set(x_1097, 0, x_1096);
lean_ctor_set(x_1097, 1, x_1095);
x_1098 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1098, 0, x_1097);
if (lean_is_scalar(x_1093)) {
 x_1099 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1099 = x_1093;
}
lean_ctor_set(x_1099, 0, x_1098);
lean_ctor_set(x_1099, 1, x_1092);
x_13 = x_1099;
goto block_28;
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
lean_dec(x_1086);
lean_dec(x_1038);
lean_dec(x_1006);
lean_dec(x_1005);
lean_dec(x_990);
x_1100 = lean_ctor_get(x_1091, 0);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_1091, 1);
lean_inc(x_1101);
if (lean_is_exclusive(x_1091)) {
 lean_ctor_release(x_1091, 0);
 lean_ctor_release(x_1091, 1);
 x_1102 = x_1091;
} else {
 lean_dec_ref(x_1091);
 x_1102 = lean_box(0);
}
if (lean_is_scalar(x_1102)) {
 x_1103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1103 = x_1102;
}
lean_ctor_set(x_1103, 0, x_1100);
lean_ctor_set(x_1103, 1, x_1101);
x_13 = x_1103;
goto block_28;
}
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
lean_dec(x_1005);
lean_dec(x_990);
x_1104 = lean_ctor_get(x_1088, 1);
lean_inc(x_1104);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1105 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1105 = lean_box(0);
}
x_1106 = lean_ctor_get(x_1089, 0);
lean_inc(x_1106);
if (lean_is_exclusive(x_1089)) {
 lean_ctor_release(x_1089, 0);
 x_1107 = x_1089;
} else {
 lean_dec_ref(x_1089);
 x_1107 = lean_box(0);
}
if (lean_is_scalar(x_1006)) {
 x_1108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1108 = x_1006;
}
lean_ctor_set(x_1108, 0, x_1038);
lean_ctor_set(x_1108, 1, x_1106);
x_1109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1109, 0, x_1007);
lean_ctor_set(x_1109, 1, x_1108);
lean_inc(x_2);
if (lean_is_scalar(x_1086)) {
 x_1110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1110 = x_1086;
}
lean_ctor_set(x_1110, 0, x_2);
lean_ctor_set(x_1110, 1, x_1109);
if (lean_is_scalar(x_1107)) {
 x_1111 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1111 = x_1107;
}
lean_ctor_set(x_1111, 0, x_1110);
if (lean_is_scalar(x_1105)) {
 x_1112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1112 = x_1105;
}
lean_ctor_set(x_1112, 0, x_1111);
lean_ctor_set(x_1112, 1, x_1104);
x_13 = x_1112;
goto block_28;
}
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; 
lean_dec(x_1086);
lean_dec(x_1038);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1005);
lean_dec(x_990);
x_1113 = lean_ctor_get(x_1088, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1088, 1);
lean_inc(x_1114);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1115 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1115 = lean_box(0);
}
if (lean_is_scalar(x_1115)) {
 x_1116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1116 = x_1115;
}
lean_ctor_set(x_1116, 0, x_1113);
lean_ctor_set(x_1116, 1, x_1114);
x_13 = x_1116;
goto block_28;
}
}
}
else
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
lean_dec(x_1038);
lean_dec(x_1013);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1005);
lean_dec(x_1004);
lean_dec(x_990);
x_1117 = lean_ctor_get(x_1048, 0);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_1048, 1);
lean_inc(x_1118);
if (lean_is_exclusive(x_1048)) {
 lean_ctor_release(x_1048, 0);
 lean_ctor_release(x_1048, 1);
 x_1119 = x_1048;
} else {
 lean_dec_ref(x_1048);
 x_1119 = lean_box(0);
}
if (lean_is_scalar(x_1119)) {
 x_1120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1120 = x_1119;
}
lean_ctor_set(x_1120, 0, x_1117);
lean_ctor_set(x_1120, 1, x_1118);
x_13 = x_1120;
goto block_28;
}
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
lean_dec(x_1038);
lean_dec(x_1013);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1005);
lean_dec(x_1004);
lean_dec(x_990);
x_1121 = lean_ctor_get(x_1040, 0);
lean_inc(x_1121);
x_1122 = lean_ctor_get(x_1040, 1);
lean_inc(x_1122);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1123 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1123 = lean_box(0);
}
if (lean_is_scalar(x_1123)) {
 x_1124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1124 = x_1123;
}
lean_ctor_set(x_1124, 0, x_1121);
lean_ctor_set(x_1124, 1, x_1122);
x_13 = x_1124;
goto block_28;
}
}
else
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
lean_dec(x_1013);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1005);
lean_dec(x_1004);
lean_dec(x_990);
x_1125 = lean_ctor_get(x_1037, 0);
lean_inc(x_1125);
x_1126 = lean_ctor_get(x_1037, 1);
lean_inc(x_1126);
if (lean_is_exclusive(x_1037)) {
 lean_ctor_release(x_1037, 0);
 lean_ctor_release(x_1037, 1);
 x_1127 = x_1037;
} else {
 lean_dec_ref(x_1037);
 x_1127 = lean_box(0);
}
if (lean_is_scalar(x_1127)) {
 x_1128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1128 = x_1127;
}
lean_ctor_set(x_1128, 0, x_1125);
lean_ctor_set(x_1128, 1, x_1126);
x_13 = x_1128;
goto block_28;
}
}
else
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
lean_dec(x_1013);
x_1129 = lean_ctor_get(x_1010, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1010, 1);
lean_inc(x_1130);
if (lean_is_exclusive(x_1010)) {
 lean_ctor_release(x_1010, 0);
 lean_ctor_release(x_1010, 1);
 x_1131 = x_1010;
} else {
 lean_dec_ref(x_1010);
 x_1131 = lean_box(0);
}
lean_inc(x_1011);
if (lean_is_scalar(x_1012)) {
 x_1132 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1132 = x_1012;
}
lean_ctor_set(x_1132, 0, x_1008);
lean_ctor_set(x_1132, 1, x_1009);
lean_ctor_set(x_1132, 2, x_1130);
lean_ctor_set(x_1132, 3, x_1011);
x_1133 = lean_st_ref_take(x_4, x_1032);
x_1134 = lean_ctor_get(x_1133, 1);
lean_inc(x_1134);
if (lean_is_exclusive(x_1133)) {
 lean_ctor_release(x_1133, 0);
 lean_ctor_release(x_1133, 1);
 x_1135 = x_1133;
} else {
 lean_dec_ref(x_1133);
 x_1135 = lean_box(0);
}
if (lean_is_scalar(x_1131)) {
 x_1136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1136 = x_1131;
}
lean_ctor_set(x_1136, 0, x_1132);
lean_ctor_set(x_1136, 1, x_1007);
if (lean_is_scalar(x_1135)) {
 x_1137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1137 = x_1135;
}
lean_ctor_set(x_1137, 0, x_1129);
lean_ctor_set(x_1137, 1, x_1136);
x_1138 = lean_st_ref_set(x_4, x_1137, x_1134);
x_1139 = lean_ctor_get(x_1138, 1);
lean_inc(x_1139);
if (lean_is_exclusive(x_1138)) {
 lean_ctor_release(x_1138, 0);
 lean_ctor_release(x_1138, 1);
 x_1140 = x_1138;
} else {
 lean_dec_ref(x_1138);
 x_1140 = lean_box(0);
}
x_1141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1141, 0, x_1011);
x_1142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1142, 0, x_1141);
if (lean_is_scalar(x_1006)) {
 x_1143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1143 = x_1006;
}
lean_ctor_set(x_1143, 0, x_1004);
lean_ctor_set(x_1143, 1, x_1005);
x_1144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1144, 0, x_990);
lean_ctor_set(x_1144, 1, x_1143);
if (lean_is_scalar(x_1033)) {
 x_1145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1145 = x_1033;
}
lean_ctor_set(x_1145, 0, x_1142);
lean_ctor_set(x_1145, 1, x_1144);
x_1146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1146, 0, x_1145);
if (lean_is_scalar(x_1140)) {
 x_1147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1147 = x_1140;
}
lean_ctor_set(x_1147, 0, x_1146);
lean_ctor_set(x_1147, 1, x_1139);
x_13 = x_1147;
goto block_28;
}
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
lean_dec(x_1033);
lean_dec(x_1012);
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_990);
lean_inc(x_1004);
x_1148 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_1148, 0, x_1013);
lean_closure_set(x_1148, 1, x_1004);
lean_inc(x_1);
x_1149 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_1149, 0, x_1);
lean_closure_set(x_1149, 1, x_1148);
x_1150 = l_Lean_Meta_Grind_getGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_1032);
x_1151 = lean_ctor_get(x_1150, 0);
lean_inc(x_1151);
x_1152 = lean_ctor_get(x_1150, 1);
lean_inc(x_1152);
lean_dec(x_1150);
x_1153 = lean_ctor_get(x_1151, 0);
lean_inc(x_1153);
lean_dec(x_1151);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1154 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_1153, x_1149, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_1152);
if (lean_obj_tag(x_1154) == 0)
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1155 = lean_ctor_get(x_1154, 0);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1154, 1);
lean_inc(x_1156);
lean_dec(x_1154);
x_1157 = lean_ctor_get(x_1155, 1);
lean_inc(x_1157);
lean_dec(x_1155);
x_1158 = lean_st_ref_take(x_4, x_1156);
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1158, 1);
lean_inc(x_1160);
if (lean_is_exclusive(x_1158)) {
 lean_ctor_release(x_1158, 0);
 lean_ctor_release(x_1158, 1);
 x_1161 = x_1158;
} else {
 lean_dec_ref(x_1158);
 x_1161 = lean_box(0);
}
x_1162 = lean_ctor_get(x_1159, 1);
lean_inc(x_1162);
if (lean_is_exclusive(x_1159)) {
 lean_ctor_release(x_1159, 0);
 lean_ctor_release(x_1159, 1);
 x_1163 = x_1159;
} else {
 lean_dec_ref(x_1159);
 x_1163 = lean_box(0);
}
if (lean_is_scalar(x_1163)) {
 x_1164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1164 = x_1163;
}
lean_ctor_set(x_1164, 0, x_1157);
lean_ctor_set(x_1164, 1, x_1162);
x_1165 = lean_st_ref_set(x_4, x_1164, x_1160);
x_1166 = lean_ctor_get(x_1165, 1);
lean_inc(x_1166);
if (lean_is_exclusive(x_1165)) {
 lean_ctor_release(x_1165, 0);
 lean_ctor_release(x_1165, 1);
 x_1167 = x_1165;
} else {
 lean_dec_ref(x_1165);
 x_1167 = lean_box(0);
}
if (lean_is_scalar(x_1006)) {
 x_1168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1168 = x_1006;
}
lean_ctor_set(x_1168, 0, x_1004);
lean_ctor_set(x_1168, 1, x_1005);
x_1169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1169, 0, x_1007);
lean_ctor_set(x_1169, 1, x_1168);
lean_inc(x_2);
if (lean_is_scalar(x_1161)) {
 x_1170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1170 = x_1161;
}
lean_ctor_set(x_1170, 0, x_2);
lean_ctor_set(x_1170, 1, x_1169);
x_1171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1171, 0, x_1170);
if (lean_is_scalar(x_1167)) {
 x_1172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1172 = x_1167;
}
lean_ctor_set(x_1172, 0, x_1171);
lean_ctor_set(x_1172, 1, x_1166);
x_13 = x_1172;
goto block_28;
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1005);
lean_dec(x_1004);
x_1173 = lean_ctor_get(x_1154, 0);
lean_inc(x_1173);
x_1174 = lean_ctor_get(x_1154, 1);
lean_inc(x_1174);
if (lean_is_exclusive(x_1154)) {
 lean_ctor_release(x_1154, 0);
 lean_ctor_release(x_1154, 1);
 x_1175 = x_1154;
} else {
 lean_dec_ref(x_1154);
 x_1175 = lean_box(0);
}
if (lean_is_scalar(x_1175)) {
 x_1176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1176 = x_1175;
}
lean_ctor_set(x_1176, 0, x_1173);
lean_ctor_set(x_1176, 1, x_1174);
x_13 = x_1176;
goto block_28;
}
}
}
else
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
lean_dec(x_1013);
lean_dec(x_1012);
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_1005);
lean_dec(x_1004);
lean_dec(x_990);
x_1177 = lean_ctor_get(x_1020, 0);
lean_inc(x_1177);
x_1178 = lean_ctor_get(x_1020, 1);
lean_inc(x_1178);
if (lean_is_exclusive(x_1020)) {
 lean_ctor_release(x_1020, 0);
 lean_ctor_release(x_1020, 1);
 x_1179 = x_1020;
} else {
 lean_dec_ref(x_1020);
 x_1179 = lean_box(0);
}
if (lean_is_scalar(x_1179)) {
 x_1180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1180 = x_1179;
}
lean_ctor_set(x_1180, 0, x_1177);
lean_ctor_set(x_1180, 1, x_1178);
x_13 = x_1180;
goto block_28;
}
}
}
block_28:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_3 = x_22;
x_12 = x_21;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__3___boxed), 11, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_Grind_getGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_17, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_23 = lean_st_ref_take(x_2, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_22);
x_28 = lean_st_ref_set(x_2, x_24, x_25);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_21);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_st_ref_set(x_2, x_34, x_25);
lean_dec(x_2);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_28, 1);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_33, 0, x_38);
x_12 = x_33;
goto block_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_28);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
x_12 = x_43;
goto block_27;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_28, 1, x_49);
x_50 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_28);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
x_12 = x_53;
goto block_27;
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_28, 1);
x_55 = lean_ctor_get(x_30, 0);
lean_inc(x_55);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 1);
x_59 = lean_ctor_get(x_30, 1);
lean_inc(x_59);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
x_63 = lean_ctor_get(x_55, 2);
x_64 = lean_ctor_get(x_55, 3);
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_inc(x_65);
x_66 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1___boxed), 11, 1);
lean_closure_set(x_66, 0, x_65);
x_67 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_68 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_68, 0, x_67);
lean_closure_set(x_68, 1, x_66);
x_69 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_73 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_72, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_st_ref_take(x_3, x_75);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
lean_ctor_set(x_79, 0, x_77);
x_83 = lean_st_ref_set(x_3, x_79, x_80);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_83, 1);
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
lean_dec(x_76);
x_88 = lean_local_ctx_num_indices(x_87);
x_89 = lean_nat_dec_lt(x_58, x_88);
lean_dec(x_88);
if (x_89 == 0)
{
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_90; 
lean_free_object(x_83);
lean_free_object(x_55);
lean_dec(x_64);
lean_dec(x_61);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_90 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_85);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_91);
lean_inc(x_65);
x_93 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_65, x_91, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
lean_inc(x_65);
x_95 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_95, 0, x_65);
x_96 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_96, 0, x_67);
lean_closure_set(x_96, 1, x_95);
x_97 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_94);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_101 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_100, x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_st_ref_take(x_3, x_103);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_110 = lean_ctor_get(x_107, 0);
lean_dec(x_110);
lean_ctor_set(x_107, 0, x_105);
x_111 = lean_st_ref_set(x_3, x_107, x_108);
x_112 = lean_unbox(x_104);
lean_dec(x_104);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_91);
lean_dec(x_65);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_st_ref_take(x_3, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_115, 1);
lean_dec(x_118);
lean_ctor_set(x_115, 1, x_59);
x_119 = lean_st_ref_set(x_3, x_115, x_116);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_119, 1);
x_122 = lean_ctor_get(x_119, 0);
lean_dec(x_122);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_123 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_121);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_119, 1, x_28);
lean_ctor_set(x_119, 0, x_126);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_119);
lean_ctor_set(x_123, 0, x_127);
x_12 = x_123;
goto block_27;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_123, 0);
x_129 = lean_ctor_get(x_123, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_123);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_119, 1, x_28);
lean_ctor_set(x_119, 0, x_130);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_119);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
x_12 = x_132;
goto block_27;
}
}
else
{
uint8_t x_133; 
lean_free_object(x_119);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_133 = !lean_is_exclusive(x_123);
if (x_133 == 0)
{
x_12 = x_123;
goto block_27;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_123, 0);
x_135 = lean_ctor_get(x_123, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_123);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_12 = x_136;
goto block_27;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_119, 1);
lean_inc(x_137);
lean_dec(x_119);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_138 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_139);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_28);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
if (lean_is_scalar(x_141)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_141;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_140);
x_12 = x_145;
goto block_27;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_146 = lean_ctor_get(x_138, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_138, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_148 = x_138;
} else {
 lean_dec_ref(x_138);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
x_12 = x_149;
goto block_27;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_150 = lean_ctor_get(x_115, 0);
lean_inc(x_150);
lean_dec(x_115);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_59);
x_152 = lean_st_ref_set(x_3, x_151, x_116);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_155 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_153);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_156);
if (lean_is_scalar(x_154)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_154;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_28);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
if (lean_is_scalar(x_158)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_158;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_157);
x_12 = x_162;
goto block_27;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_154);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_163 = lean_ctor_get(x_155, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_155, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_165 = x_155;
} else {
 lean_dec_ref(x_155);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
x_12 = x_166;
goto block_27;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_57);
x_167 = !lean_is_exclusive(x_111);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_111, 1);
x_169 = lean_ctor_get(x_111, 0);
lean_dec(x_169);
lean_inc(x_91);
x_170 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_170, 0, x_91);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_171 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_65, x_170, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_168);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_59);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_91);
x_174 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_91, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_173);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_174, 0);
lean_dec(x_176);
lean_ctor_set(x_54, 0, x_91);
x_177 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
lean_ctor_set(x_111, 1, x_28);
lean_ctor_set(x_111, 0, x_177);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_111);
lean_ctor_set(x_174, 0, x_178);
x_12 = x_174;
goto block_27;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_174, 1);
lean_inc(x_179);
lean_dec(x_174);
lean_ctor_set(x_54, 0, x_91);
x_180 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
lean_ctor_set(x_111, 1, x_28);
lean_ctor_set(x_111, 0, x_180);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_111);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_179);
x_12 = x_182;
goto block_27;
}
}
else
{
uint8_t x_183; 
lean_free_object(x_111);
lean_dec(x_91);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_183 = !lean_is_exclusive(x_174);
if (x_183 == 0)
{
x_12 = x_174;
goto block_27;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_174, 0);
x_185 = lean_ctor_get(x_174, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_174);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_12 = x_186;
goto block_27;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_58);
lean_dec(x_30);
x_187 = !lean_is_exclusive(x_171);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_171, 0);
lean_dec(x_188);
x_189 = !lean_is_exclusive(x_172);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_172, 0);
lean_ctor_set(x_54, 1, x_190);
lean_ctor_set(x_54, 0, x_91);
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
lean_ctor_set(x_111, 1, x_28);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_172, 0, x_111);
x_12 = x_171;
goto block_27;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_172, 0);
lean_inc(x_191);
lean_dec(x_172);
lean_ctor_set(x_54, 1, x_191);
lean_ctor_set(x_54, 0, x_91);
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
lean_ctor_set(x_111, 1, x_28);
lean_ctor_set(x_111, 0, x_1);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_111);
lean_ctor_set(x_171, 0, x_192);
x_12 = x_171;
goto block_27;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_171, 1);
lean_inc(x_193);
lean_dec(x_171);
x_194 = lean_ctor_get(x_172, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_195 = x_172;
} else {
 lean_dec_ref(x_172);
 x_195 = lean_box(0);
}
lean_ctor_set(x_54, 1, x_194);
lean_ctor_set(x_54, 0, x_91);
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
lean_ctor_set(x_111, 1, x_28);
lean_ctor_set(x_111, 0, x_1);
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 1, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_111);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_193);
x_12 = x_197;
goto block_27;
}
}
}
else
{
uint8_t x_198; 
lean_free_object(x_111);
lean_dec(x_91);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_198 = !lean_is_exclusive(x_171);
if (x_198 == 0)
{
x_12 = x_171;
goto block_27;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_171, 0);
x_200 = lean_ctor_get(x_171, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_171);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_12 = x_201;
goto block_27;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_111, 1);
lean_inc(x_202);
lean_dec(x_111);
lean_inc(x_91);
x_203 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_203, 0, x_91);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_204 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_65, x_203, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_202);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_59);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_91);
x_207 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_91, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_91);
x_210 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_28);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
if (lean_is_scalar(x_209)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_209;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_208);
x_12 = x_213;
goto block_27;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_91);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_214 = lean_ctor_get(x_207, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_207, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_216 = x_207;
} else {
 lean_dec_ref(x_207);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
x_12 = x_217;
goto block_27;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_58);
lean_dec(x_30);
x_218 = lean_ctor_get(x_204, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_219 = x_204;
} else {
 lean_dec_ref(x_204);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_205, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 x_221 = x_205;
} else {
 lean_dec_ref(x_205);
 x_221 = lean_box(0);
}
lean_ctor_set(x_54, 1, x_220);
lean_ctor_set(x_54, 0, x_91);
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_1);
lean_ctor_set(x_222, 1, x_28);
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_222);
if (lean_is_scalar(x_219)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_219;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_218);
x_12 = x_224;
goto block_27;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_91);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_225 = lean_ctor_get(x_204, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_204, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_227 = x_204;
} else {
 lean_dec_ref(x_204);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
x_12 = x_228;
goto block_27;
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_229 = lean_ctor_get(x_107, 1);
lean_inc(x_229);
lean_dec(x_107);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_105);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_st_ref_set(x_3, x_230, x_108);
x_232 = lean_unbox(x_104);
lean_dec(x_104);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_91);
lean_dec(x_65);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_st_ref_take(x_3, x_233);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_59);
x_240 = lean_st_ref_set(x_3, x_239, x_236);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_242 = x_240;
} else {
 lean_dec_ref(x_240);
 x_242 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_243 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_241);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_244);
if (lean_is_scalar(x_242)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_242;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_28);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
if (lean_is_scalar(x_246)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_246;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_245);
x_12 = x_250;
goto block_27;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_242);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_251 = lean_ctor_get(x_243, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_243, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_253 = x_243;
} else {
 lean_dec_ref(x_243);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
x_12 = x_254;
goto block_27;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_57);
x_255 = lean_ctor_get(x_231, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_256 = x_231;
} else {
 lean_dec_ref(x_231);
 x_256 = lean_box(0);
}
lean_inc(x_91);
x_257 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_257, 0, x_91);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_258 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_65, x_257, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_255);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_59);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_91);
x_261 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_91, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_91);
x_264 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_256)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_256;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_28);
x_266 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_266, 0, x_265);
if (lean_is_scalar(x_263)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_263;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_262);
x_12 = x_267;
goto block_27;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_256);
lean_dec(x_91);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_268 = lean_ctor_get(x_261, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_261, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_270 = x_261;
} else {
 lean_dec_ref(x_261);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
x_12 = x_271;
goto block_27;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_58);
lean_dec(x_30);
x_272 = lean_ctor_get(x_258, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_273 = x_258;
} else {
 lean_dec_ref(x_258);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_259, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_275 = x_259;
} else {
 lean_dec_ref(x_259);
 x_275 = lean_box(0);
}
lean_ctor_set(x_54, 1, x_274);
lean_ctor_set(x_54, 0, x_91);
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
if (lean_is_scalar(x_256)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_256;
}
lean_ctor_set(x_276, 0, x_1);
lean_ctor_set(x_276, 1, x_28);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_275;
}
lean_ctor_set(x_277, 0, x_276);
if (lean_is_scalar(x_273)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_273;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_272);
x_12 = x_278;
goto block_27;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_256);
lean_dec(x_91);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_279 = lean_ctor_get(x_258, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_258, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_281 = x_258;
} else {
 lean_dec_ref(x_258);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
x_12 = x_282;
goto block_27;
}
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_91);
lean_dec(x_65);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_283 = !lean_is_exclusive(x_101);
if (x_283 == 0)
{
x_12 = x_101;
goto block_27;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_101, 0);
x_285 = lean_ctor_get(x_101, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_101);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_12 = x_286;
goto block_27;
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_91);
lean_dec(x_65);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_287 = !lean_is_exclusive(x_93);
if (x_287 == 0)
{
x_12 = x_93;
goto block_27;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_93, 0);
x_289 = lean_ctor_get(x_93, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_93);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
x_12 = x_290;
goto block_27;
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_65);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_291 = !lean_is_exclusive(x_90);
if (x_291 == 0)
{
x_12 = x_90;
goto block_27;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_90, 0);
x_293 = lean_ctor_get(x_90, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_90);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_12 = x_294;
goto block_27;
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_65);
x_295 = !lean_is_exclusive(x_63);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_296 = lean_ctor_get(x_63, 0);
x_297 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_ctor_set(x_55, 2, x_297);
x_298 = lean_st_ref_take(x_3, x_85);
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_300 = lean_ctor_get(x_298, 1);
x_301 = lean_ctor_get(x_298, 0);
lean_dec(x_301);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 0, x_55);
lean_ctor_set(x_298, 1, x_63);
lean_ctor_set(x_298, 0, x_296);
x_302 = lean_st_ref_set(x_3, x_298, x_300);
x_303 = !lean_is_exclusive(x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_302, 0);
lean_dec(x_304);
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_64);
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_83, 1, x_28);
lean_ctor_set(x_83, 0, x_306);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_83);
lean_ctor_set(x_302, 0, x_307);
x_12 = x_302;
goto block_27;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_308 = lean_ctor_get(x_302, 1);
lean_inc(x_308);
lean_dec(x_302);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_64);
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_83, 1, x_28);
lean_ctor_set(x_83, 0, x_310);
x_311 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_311, 0, x_83);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_308);
x_12 = x_312;
goto block_27;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_313 = lean_ctor_get(x_298, 1);
lean_inc(x_313);
lean_dec(x_298);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 0, x_55);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_296);
lean_ctor_set(x_314, 1, x_63);
x_315 = lean_st_ref_set(x_3, x_314, x_313);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_64);
x_319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_83, 1, x_28);
lean_ctor_set(x_83, 0, x_319);
x_320 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_320, 0, x_83);
if (lean_is_scalar(x_317)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_317;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_316);
x_12 = x_321;
goto block_27;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_322 = lean_ctor_get(x_63, 0);
x_323 = lean_ctor_get(x_63, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_63);
lean_inc(x_64);
lean_ctor_set(x_55, 2, x_323);
x_324 = lean_st_ref_take(x_3, x_85);
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_326 = x_324;
} else {
 lean_dec_ref(x_324);
 x_326 = lean_box(0);
}
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_55);
lean_ctor_set(x_327, 1, x_59);
if (lean_is_scalar(x_326)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_326;
}
lean_ctor_set(x_328, 0, x_322);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_st_ref_set(x_3, x_328, x_325);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_331 = x_329;
} else {
 lean_dec_ref(x_329);
 x_331 = lean_box(0);
}
x_332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_332, 0, x_64);
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_83, 1, x_28);
lean_ctor_set(x_83, 0, x_333);
x_334 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_334, 0, x_83);
if (lean_is_scalar(x_331)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_331;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_330);
x_12 = x_335;
goto block_27;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_free_object(x_83);
lean_free_object(x_55);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_30);
lean_inc(x_57);
x_336 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_336, 0, x_65);
lean_closure_set(x_336, 1, x_57);
x_337 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_337, 0, x_67);
lean_closure_set(x_337, 1, x_336);
x_338 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_85);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
lean_dec(x_339);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_342 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_341, x_337, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_340);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_st_ref_take(x_3, x_344);
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
lean_object* x_348; uint8_t x_349; 
x_348 = lean_ctor_get(x_346, 0);
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_350 = lean_ctor_get(x_346, 1);
x_351 = lean_ctor_get(x_348, 0);
lean_dec(x_351);
lean_ctor_set(x_348, 0, x_345);
x_352 = lean_st_ref_set(x_3, x_348, x_350);
x_353 = !lean_is_exclusive(x_352);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_352, 0);
lean_dec(x_354);
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
lean_ctor_set(x_346, 1, x_28);
lean_ctor_set(x_346, 0, x_1);
x_355 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_355, 0, x_346);
lean_ctor_set(x_352, 0, x_355);
x_12 = x_352;
goto block_27;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
lean_dec(x_352);
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
lean_ctor_set(x_346, 1, x_28);
lean_ctor_set(x_346, 0, x_1);
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_346);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
x_12 = x_358;
goto block_27;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_359 = lean_ctor_get(x_346, 1);
x_360 = lean_ctor_get(x_348, 1);
lean_inc(x_360);
lean_dec(x_348);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_345);
lean_ctor_set(x_361, 1, x_360);
x_362 = lean_st_ref_set(x_3, x_361, x_359);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_364 = x_362;
} else {
 lean_dec_ref(x_362);
 x_364 = lean_box(0);
}
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
lean_ctor_set(x_346, 1, x_28);
lean_ctor_set(x_346, 0, x_1);
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_346);
if (lean_is_scalar(x_364)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_364;
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_363);
x_12 = x_366;
goto block_27;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_367 = lean_ctor_get(x_346, 0);
x_368 = lean_ctor_get(x_346, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_346);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_370 = x_367;
} else {
 lean_dec_ref(x_367);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_345);
lean_ctor_set(x_371, 1, x_369);
x_372 = lean_st_ref_set(x_3, x_371, x_368);
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_1);
lean_ctor_set(x_375, 1, x_28);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_375);
if (lean_is_scalar(x_374)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_374;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_373);
x_12 = x_377;
goto block_27;
}
}
else
{
uint8_t x_378; 
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
x_378 = !lean_is_exclusive(x_342);
if (x_378 == 0)
{
x_12 = x_342;
goto block_27;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_342, 0);
x_380 = lean_ctor_get(x_342, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_342);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
x_12 = x_381;
goto block_27;
}
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_382 = lean_ctor_get(x_83, 1);
lean_inc(x_382);
lean_dec(x_83);
x_383 = lean_ctor_get(x_76, 1);
lean_inc(x_383);
lean_dec(x_76);
x_384 = lean_local_ctx_num_indices(x_383);
x_385 = lean_nat_dec_lt(x_58, x_384);
lean_dec(x_384);
if (x_385 == 0)
{
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_386; 
lean_free_object(x_55);
lean_dec(x_64);
lean_dec(x_61);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_386 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_382);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_387);
lean_inc(x_65);
x_389 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_65, x_387, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_388);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
lean_dec(x_389);
lean_inc(x_65);
x_391 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_391, 0, x_65);
x_392 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_392, 0, x_67);
lean_closure_set(x_392, 1, x_391);
x_393 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_390);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_ctor_get(x_394, 0);
lean_inc(x_396);
lean_dec(x_394);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_397 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_396, x_392, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_395);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_ctor_get(x_398, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_398, 1);
lean_inc(x_401);
lean_dec(x_398);
x_402 = lean_st_ref_take(x_3, x_399);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_406 = x_403;
} else {
 lean_dec_ref(x_403);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_401);
lean_ctor_set(x_407, 1, x_405);
x_408 = lean_st_ref_set(x_3, x_407, x_404);
x_409 = lean_unbox(x_400);
lean_dec(x_400);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_387);
lean_dec(x_65);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_st_ref_take(x_3, x_410);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_ctor_get(x_412, 0);
lean_inc(x_414);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_415 = x_412;
} else {
 lean_dec_ref(x_412);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_59);
x_417 = lean_st_ref_set(x_3, x_416, x_413);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_419 = x_417;
} else {
 lean_dec_ref(x_417);
 x_419 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_420 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_418);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_423 = x_420;
} else {
 lean_dec_ref(x_420);
 x_423 = lean_box(0);
}
x_424 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_424, 0, x_421);
if (lean_is_scalar(x_419)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_419;
}
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_28);
x_426 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_426, 0, x_425);
if (lean_is_scalar(x_423)) {
 x_427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_427 = x_423;
}
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_422);
x_12 = x_427;
goto block_27;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_419);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_428 = lean_ctor_get(x_420, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_420, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_430 = x_420;
} else {
 lean_dec_ref(x_420);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_428);
lean_ctor_set(x_431, 1, x_429);
x_12 = x_431;
goto block_27;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_57);
x_432 = lean_ctor_get(x_408, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_433 = x_408;
} else {
 lean_dec_ref(x_408);
 x_433 = lean_box(0);
}
lean_inc(x_387);
x_434 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_434, 0, x_387);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_435 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_65, x_434, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_432);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; 
lean_dec(x_59);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_387);
x_438 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_387, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_437);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_440 = x_438;
} else {
 lean_dec_ref(x_438);
 x_440 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_387);
x_441 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_433)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_433;
}
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_28);
x_443 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_443, 0, x_442);
if (lean_is_scalar(x_440)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_440;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_439);
x_12 = x_444;
goto block_27;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_433);
lean_dec(x_387);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_445 = lean_ctor_get(x_438, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_438, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_447 = x_438;
} else {
 lean_dec_ref(x_438);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
x_12 = x_448;
goto block_27;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_58);
lean_dec(x_30);
x_449 = lean_ctor_get(x_435, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_450 = x_435;
} else {
 lean_dec_ref(x_435);
 x_450 = lean_box(0);
}
x_451 = lean_ctor_get(x_436, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_452 = x_436;
} else {
 lean_dec_ref(x_436);
 x_452 = lean_box(0);
}
lean_ctor_set(x_54, 1, x_451);
lean_ctor_set(x_54, 0, x_387);
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
if (lean_is_scalar(x_433)) {
 x_453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_453 = x_433;
}
lean_ctor_set(x_453, 0, x_1);
lean_ctor_set(x_453, 1, x_28);
if (lean_is_scalar(x_452)) {
 x_454 = lean_alloc_ctor(1, 1, 0);
} else {
 x_454 = x_452;
}
lean_ctor_set(x_454, 0, x_453);
if (lean_is_scalar(x_450)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_450;
}
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_449);
x_12 = x_455;
goto block_27;
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_433);
lean_dec(x_387);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_456 = lean_ctor_get(x_435, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_435, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_458 = x_435;
} else {
 lean_dec_ref(x_435);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_456);
lean_ctor_set(x_459, 1, x_457);
x_12 = x_459;
goto block_27;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_387);
lean_dec(x_65);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_460 = lean_ctor_get(x_397, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_397, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_462 = x_397;
} else {
 lean_dec_ref(x_397);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_461);
x_12 = x_463;
goto block_27;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_387);
lean_dec(x_65);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_464 = lean_ctor_get(x_389, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_389, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_466 = x_389;
} else {
 lean_dec_ref(x_389);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_464);
lean_ctor_set(x_467, 1, x_465);
x_12 = x_467;
goto block_27;
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_65);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_468 = lean_ctor_get(x_386, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_386, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_470 = x_386;
} else {
 lean_dec_ref(x_386);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set(x_471, 1, x_469);
x_12 = x_471;
goto block_27;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec(x_65);
x_472 = lean_ctor_get(x_63, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_63, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_474 = x_63;
} else {
 lean_dec_ref(x_63);
 x_474 = lean_box(0);
}
lean_inc(x_64);
lean_ctor_set(x_55, 2, x_473);
x_475 = lean_st_ref_take(x_3, x_382);
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_477 = x_475;
} else {
 lean_dec_ref(x_475);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_474;
}
lean_ctor_set(x_478, 0, x_55);
lean_ctor_set(x_478, 1, x_59);
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_477;
}
lean_ctor_set(x_479, 0, x_472);
lean_ctor_set(x_479, 1, x_478);
x_480 = lean_st_ref_set(x_3, x_479, x_476);
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_482 = x_480;
} else {
 lean_dec_ref(x_480);
 x_482 = lean_box(0);
}
x_483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_483, 0, x_64);
x_484 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_484, 0, x_483);
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_28);
x_486 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_486, 0, x_485);
if (lean_is_scalar(x_482)) {
 x_487 = lean_alloc_ctor(0, 2, 0);
} else {
 x_487 = x_482;
}
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_481);
x_12 = x_487;
goto block_27;
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_free_object(x_55);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_30);
lean_inc(x_57);
x_488 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_488, 0, x_65);
lean_closure_set(x_488, 1, x_57);
x_489 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_489, 0, x_67);
lean_closure_set(x_489, 1, x_488);
x_490 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_382);
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
x_493 = lean_ctor_get(x_491, 0);
lean_inc(x_493);
lean_dec(x_491);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_494 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_493, x_489, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_492);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_498 = lean_st_ref_take(x_3, x_496);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_501 = x_498;
} else {
 lean_dec_ref(x_498);
 x_501 = lean_box(0);
}
x_502 = lean_ctor_get(x_499, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_503 = x_499;
} else {
 lean_dec_ref(x_499);
 x_503 = lean_box(0);
}
if (lean_is_scalar(x_503)) {
 x_504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_504 = x_503;
}
lean_ctor_set(x_504, 0, x_497);
lean_ctor_set(x_504, 1, x_502);
x_505 = lean_st_ref_set(x_3, x_504, x_500);
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_507 = x_505;
} else {
 lean_dec_ref(x_505);
 x_507 = lean_box(0);
}
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
if (lean_is_scalar(x_501)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_501;
}
lean_ctor_set(x_508, 0, x_1);
lean_ctor_set(x_508, 1, x_28);
x_509 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_509, 0, x_508);
if (lean_is_scalar(x_507)) {
 x_510 = lean_alloc_ctor(0, 2, 0);
} else {
 x_510 = x_507;
}
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_506);
x_12 = x_510;
goto block_27;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
x_511 = lean_ctor_get(x_494, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_494, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_513 = x_494;
} else {
 lean_dec_ref(x_494);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_512);
x_12 = x_514;
goto block_27;
}
}
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
x_515 = lean_ctor_get(x_79, 1);
lean_inc(x_515);
lean_dec(x_79);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_77);
lean_ctor_set(x_516, 1, x_515);
x_517 = lean_st_ref_set(x_3, x_516, x_80);
x_518 = lean_ctor_get(x_517, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 lean_ctor_release(x_517, 1);
 x_519 = x_517;
} else {
 lean_dec_ref(x_517);
 x_519 = lean_box(0);
}
x_520 = lean_ctor_get(x_76, 1);
lean_inc(x_520);
lean_dec(x_76);
x_521 = lean_local_ctx_num_indices(x_520);
x_522 = lean_nat_dec_lt(x_58, x_521);
lean_dec(x_521);
if (x_522 == 0)
{
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_523; 
lean_dec(x_519);
lean_free_object(x_55);
lean_dec(x_64);
lean_dec(x_61);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_523 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_518);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_524);
lean_inc(x_65);
x_526 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_65, x_524, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_525);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_527 = lean_ctor_get(x_526, 1);
lean_inc(x_527);
lean_dec(x_526);
lean_inc(x_65);
x_528 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_528, 0, x_65);
x_529 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_529, 0, x_67);
lean_closure_set(x_529, 1, x_528);
x_530 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_527);
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = lean_ctor_get(x_531, 0);
lean_inc(x_533);
lean_dec(x_531);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_534 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_533, x_529, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_532);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_537 = lean_ctor_get(x_535, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_535, 1);
lean_inc(x_538);
lean_dec(x_535);
x_539 = lean_st_ref_take(x_3, x_536);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_543 = x_540;
} else {
 lean_dec_ref(x_540);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_538);
lean_ctor_set(x_544, 1, x_542);
x_545 = lean_st_ref_set(x_3, x_544, x_541);
x_546 = lean_unbox(x_537);
lean_dec(x_537);
if (x_546 == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_524);
lean_dec(x_65);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
lean_dec(x_545);
x_548 = lean_st_ref_take(x_3, x_547);
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_551 = lean_ctor_get(x_549, 0);
lean_inc(x_551);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_552 = x_549;
} else {
 lean_dec_ref(x_549);
 x_552 = lean_box(0);
}
if (lean_is_scalar(x_552)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_552;
}
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_59);
x_554 = lean_st_ref_set(x_3, x_553, x_550);
x_555 = lean_ctor_get(x_554, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_556 = x_554;
} else {
 lean_dec_ref(x_554);
 x_556 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_557 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_555);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_560 = x_557;
} else {
 lean_dec_ref(x_557);
 x_560 = lean_box(0);
}
x_561 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_561, 0, x_558);
if (lean_is_scalar(x_556)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_556;
}
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_28);
x_563 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_563, 0, x_562);
if (lean_is_scalar(x_560)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_560;
}
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_559);
x_12 = x_564;
goto block_27;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_556);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_565 = lean_ctor_get(x_557, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_557, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_567 = x_557;
} else {
 lean_dec_ref(x_557);
 x_567 = lean_box(0);
}
if (lean_is_scalar(x_567)) {
 x_568 = lean_alloc_ctor(1, 2, 0);
} else {
 x_568 = x_567;
}
lean_ctor_set(x_568, 0, x_565);
lean_ctor_set(x_568, 1, x_566);
x_12 = x_568;
goto block_27;
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
lean_dec(x_57);
x_569 = lean_ctor_get(x_545, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_570 = x_545;
} else {
 lean_dec_ref(x_545);
 x_570 = lean_box(0);
}
lean_inc(x_524);
x_571 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_571, 0, x_524);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_572 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_65, x_571, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_569);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; 
lean_dec(x_59);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_524);
x_575 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_524, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_574);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_576 = lean_ctor_get(x_575, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_577 = x_575;
} else {
 lean_dec_ref(x_575);
 x_577 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_524);
x_578 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_570)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_570;
}
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_28);
x_580 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_580, 0, x_579);
if (lean_is_scalar(x_577)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_577;
}
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_576);
x_12 = x_581;
goto block_27;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
lean_dec(x_570);
lean_dec(x_524);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_582 = lean_ctor_get(x_575, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_575, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_584 = x_575;
} else {
 lean_dec_ref(x_575);
 x_584 = lean_box(0);
}
if (lean_is_scalar(x_584)) {
 x_585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_585 = x_584;
}
lean_ctor_set(x_585, 0, x_582);
lean_ctor_set(x_585, 1, x_583);
x_12 = x_585;
goto block_27;
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_58);
lean_dec(x_30);
x_586 = lean_ctor_get(x_572, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_587 = x_572;
} else {
 lean_dec_ref(x_572);
 x_587 = lean_box(0);
}
x_588 = lean_ctor_get(x_573, 0);
lean_inc(x_588);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 x_589 = x_573;
} else {
 lean_dec_ref(x_573);
 x_589 = lean_box(0);
}
lean_ctor_set(x_54, 1, x_588);
lean_ctor_set(x_54, 0, x_524);
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
if (lean_is_scalar(x_570)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_570;
}
lean_ctor_set(x_590, 0, x_1);
lean_ctor_set(x_590, 1, x_28);
if (lean_is_scalar(x_589)) {
 x_591 = lean_alloc_ctor(1, 1, 0);
} else {
 x_591 = x_589;
}
lean_ctor_set(x_591, 0, x_590);
if (lean_is_scalar(x_587)) {
 x_592 = lean_alloc_ctor(0, 2, 0);
} else {
 x_592 = x_587;
}
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_586);
x_12 = x_592;
goto block_27;
}
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_570);
lean_dec(x_524);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_593 = lean_ctor_get(x_572, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_572, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_595 = x_572;
} else {
 lean_dec_ref(x_572);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_593);
lean_ctor_set(x_596, 1, x_594);
x_12 = x_596;
goto block_27;
}
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_524);
lean_dec(x_65);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_597 = lean_ctor_get(x_534, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_534, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_599 = x_534;
} else {
 lean_dec_ref(x_534);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(1, 2, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_597);
lean_ctor_set(x_600, 1, x_598);
x_12 = x_600;
goto block_27;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_524);
lean_dec(x_65);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_601 = lean_ctor_get(x_526, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_526, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_603 = x_526;
} else {
 lean_dec_ref(x_526);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_601);
lean_ctor_set(x_604, 1, x_602);
x_12 = x_604;
goto block_27;
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
lean_dec(x_65);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_605 = lean_ctor_get(x_523, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_523, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_607 = x_523;
} else {
 lean_dec_ref(x_523);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_607)) {
 x_608 = lean_alloc_ctor(1, 2, 0);
} else {
 x_608 = x_607;
}
lean_ctor_set(x_608, 0, x_605);
lean_ctor_set(x_608, 1, x_606);
x_12 = x_608;
goto block_27;
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_65);
x_609 = lean_ctor_get(x_63, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_63, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_611 = x_63;
} else {
 lean_dec_ref(x_63);
 x_611 = lean_box(0);
}
lean_inc(x_64);
lean_ctor_set(x_55, 2, x_610);
x_612 = lean_st_ref_take(x_3, x_518);
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_614 = x_612;
} else {
 lean_dec_ref(x_612);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_615 = lean_alloc_ctor(1, 2, 0);
} else {
 x_615 = x_611;
}
lean_ctor_set(x_615, 0, x_55);
lean_ctor_set(x_615, 1, x_59);
if (lean_is_scalar(x_614)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_614;
}
lean_ctor_set(x_616, 0, x_609);
lean_ctor_set(x_616, 1, x_615);
x_617 = lean_st_ref_set(x_3, x_616, x_613);
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_619 = x_617;
} else {
 lean_dec_ref(x_617);
 x_619 = lean_box(0);
}
x_620 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_620, 0, x_64);
x_621 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_621, 0, x_620);
if (lean_is_scalar(x_519)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_519;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_28);
x_623 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_623, 0, x_622);
if (lean_is_scalar(x_619)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_619;
}
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_618);
x_12 = x_624;
goto block_27;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_519);
lean_free_object(x_55);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_30);
lean_inc(x_57);
x_625 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_625, 0, x_65);
lean_closure_set(x_625, 1, x_57);
x_626 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_626, 0, x_67);
lean_closure_set(x_626, 1, x_625);
x_627 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_518);
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
lean_dec(x_627);
x_630 = lean_ctor_get(x_628, 0);
lean_inc(x_630);
lean_dec(x_628);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_631 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_630, x_626, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_629);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
lean_dec(x_631);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = lean_st_ref_take(x_3, x_633);
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_638 = x_635;
} else {
 lean_dec_ref(x_635);
 x_638 = lean_box(0);
}
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_640 = x_636;
} else {
 lean_dec_ref(x_636);
 x_640 = lean_box(0);
}
if (lean_is_scalar(x_640)) {
 x_641 = lean_alloc_ctor(0, 2, 0);
} else {
 x_641 = x_640;
}
lean_ctor_set(x_641, 0, x_634);
lean_ctor_set(x_641, 1, x_639);
x_642 = lean_st_ref_set(x_3, x_641, x_637);
x_643 = lean_ctor_get(x_642, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_644 = x_642;
} else {
 lean_dec_ref(x_642);
 x_644 = lean_box(0);
}
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
if (lean_is_scalar(x_638)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_638;
}
lean_ctor_set(x_645, 0, x_1);
lean_ctor_set(x_645, 1, x_28);
x_646 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_646, 0, x_645);
if (lean_is_scalar(x_644)) {
 x_647 = lean_alloc_ctor(0, 2, 0);
} else {
 x_647 = x_644;
}
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_643);
x_12 = x_647;
goto block_27;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
x_648 = lean_ctor_get(x_631, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_631, 1);
lean_inc(x_649);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_650 = x_631;
} else {
 lean_dec_ref(x_631);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_648);
lean_ctor_set(x_651, 1, x_649);
x_12 = x_651;
goto block_27;
}
}
}
}
else
{
uint8_t x_652; 
lean_dec(x_65);
lean_free_object(x_55);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_652 = !lean_is_exclusive(x_73);
if (x_652 == 0)
{
x_12 = x_73;
goto block_27;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_73, 0);
x_654 = lean_ctor_get(x_73, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_73);
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_653);
lean_ctor_set(x_655, 1, x_654);
x_12 = x_655;
goto block_27;
}
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_656 = lean_ctor_get(x_55, 0);
x_657 = lean_ctor_get(x_55, 1);
x_658 = lean_ctor_get(x_55, 2);
x_659 = lean_ctor_get(x_55, 3);
lean_inc(x_659);
lean_inc(x_658);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_55);
x_660 = lean_ctor_get(x_656, 0);
lean_inc(x_660);
lean_inc(x_660);
x_661 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1___boxed), 11, 1);
lean_closure_set(x_661, 0, x_660);
x_662 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_663 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_663, 0, x_662);
lean_closure_set(x_663, 1, x_661);
x_664 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
x_667 = lean_ctor_get(x_665, 0);
lean_inc(x_667);
lean_dec(x_665);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_668 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_667, x_663, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_666);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
lean_dec(x_668);
x_671 = lean_ctor_get(x_669, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_669, 1);
lean_inc(x_672);
lean_dec(x_669);
x_673 = lean_st_ref_take(x_3, x_670);
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
lean_dec(x_673);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_677 = x_674;
} else {
 lean_dec_ref(x_674);
 x_677 = lean_box(0);
}
if (lean_is_scalar(x_677)) {
 x_678 = lean_alloc_ctor(0, 2, 0);
} else {
 x_678 = x_677;
}
lean_ctor_set(x_678, 0, x_672);
lean_ctor_set(x_678, 1, x_676);
x_679 = lean_st_ref_set(x_3, x_678, x_675);
x_680 = lean_ctor_get(x_679, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_681 = x_679;
} else {
 lean_dec_ref(x_679);
 x_681 = lean_box(0);
}
x_682 = lean_ctor_get(x_671, 1);
lean_inc(x_682);
lean_dec(x_671);
x_683 = lean_local_ctx_num_indices(x_682);
x_684 = lean_nat_dec_lt(x_58, x_683);
lean_dec(x_683);
if (x_684 == 0)
{
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_685; 
lean_dec(x_681);
lean_dec(x_659);
lean_dec(x_656);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_685 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_657, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_680);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_686);
lean_inc(x_660);
x_688 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_660, x_686, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_687);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_689 = lean_ctor_get(x_688, 1);
lean_inc(x_689);
lean_dec(x_688);
lean_inc(x_660);
x_690 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_690, 0, x_660);
x_691 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_691, 0, x_662);
lean_closure_set(x_691, 1, x_690);
x_692 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_689);
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_692, 1);
lean_inc(x_694);
lean_dec(x_692);
x_695 = lean_ctor_get(x_693, 0);
lean_inc(x_695);
lean_dec(x_693);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_696 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_695, x_691, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_694);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; uint8_t x_708; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
x_699 = lean_ctor_get(x_697, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_697, 1);
lean_inc(x_700);
lean_dec(x_697);
x_701 = lean_st_ref_take(x_3, x_698);
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec(x_701);
x_704 = lean_ctor_get(x_702, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_705 = x_702;
} else {
 lean_dec_ref(x_702);
 x_705 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_706 = lean_alloc_ctor(0, 2, 0);
} else {
 x_706 = x_705;
}
lean_ctor_set(x_706, 0, x_700);
lean_ctor_set(x_706, 1, x_704);
x_707 = lean_st_ref_set(x_3, x_706, x_703);
x_708 = lean_unbox(x_699);
lean_dec(x_699);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_686);
lean_dec(x_660);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec(x_707);
x_710 = lean_st_ref_take(x_3, x_709);
x_711 = lean_ctor_get(x_710, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_710, 1);
lean_inc(x_712);
lean_dec(x_710);
x_713 = lean_ctor_get(x_711, 0);
lean_inc(x_713);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_714 = x_711;
} else {
 lean_dec_ref(x_711);
 x_714 = lean_box(0);
}
if (lean_is_scalar(x_714)) {
 x_715 = lean_alloc_ctor(0, 2, 0);
} else {
 x_715 = x_714;
}
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_59);
x_716 = lean_st_ref_set(x_3, x_715, x_712);
x_717 = lean_ctor_get(x_716, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 lean_ctor_release(x_716, 1);
 x_718 = x_716;
} else {
 lean_dec_ref(x_716);
 x_718 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_719 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_717);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_722 = x_719;
} else {
 lean_dec_ref(x_719);
 x_722 = lean_box(0);
}
x_723 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_723, 0, x_720);
if (lean_is_scalar(x_718)) {
 x_724 = lean_alloc_ctor(0, 2, 0);
} else {
 x_724 = x_718;
}
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_28);
x_725 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_725, 0, x_724);
if (lean_is_scalar(x_722)) {
 x_726 = lean_alloc_ctor(0, 2, 0);
} else {
 x_726 = x_722;
}
lean_ctor_set(x_726, 0, x_725);
lean_ctor_set(x_726, 1, x_721);
x_12 = x_726;
goto block_27;
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_718);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_727 = lean_ctor_get(x_719, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_719, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_729 = x_719;
} else {
 lean_dec_ref(x_719);
 x_729 = lean_box(0);
}
if (lean_is_scalar(x_729)) {
 x_730 = lean_alloc_ctor(1, 2, 0);
} else {
 x_730 = x_729;
}
lean_ctor_set(x_730, 0, x_727);
lean_ctor_set(x_730, 1, x_728);
x_12 = x_730;
goto block_27;
}
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_dec(x_57);
x_731 = lean_ctor_get(x_707, 1);
lean_inc(x_731);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_732 = x_707;
} else {
 lean_dec_ref(x_707);
 x_732 = lean_box(0);
}
lean_inc(x_686);
x_733 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_733, 0, x_686);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_734 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_660, x_733, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_731);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; 
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; 
lean_dec(x_59);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_686);
x_737 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_686, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_736);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_738 = lean_ctor_get(x_737, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_737)) {
 lean_ctor_release(x_737, 0);
 lean_ctor_release(x_737, 1);
 x_739 = x_737;
} else {
 lean_dec_ref(x_737);
 x_739 = lean_box(0);
}
lean_ctor_set(x_54, 0, x_686);
x_740 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_732)) {
 x_741 = lean_alloc_ctor(0, 2, 0);
} else {
 x_741 = x_732;
}
lean_ctor_set(x_741, 0, x_740);
lean_ctor_set(x_741, 1, x_28);
x_742 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_742, 0, x_741);
if (lean_is_scalar(x_739)) {
 x_743 = lean_alloc_ctor(0, 2, 0);
} else {
 x_743 = x_739;
}
lean_ctor_set(x_743, 0, x_742);
lean_ctor_set(x_743, 1, x_738);
x_12 = x_743;
goto block_27;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
lean_dec(x_732);
lean_dec(x_686);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_744 = lean_ctor_get(x_737, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_737, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_737)) {
 lean_ctor_release(x_737, 0);
 lean_ctor_release(x_737, 1);
 x_746 = x_737;
} else {
 lean_dec_ref(x_737);
 x_746 = lean_box(0);
}
if (lean_is_scalar(x_746)) {
 x_747 = lean_alloc_ctor(1, 2, 0);
} else {
 x_747 = x_746;
}
lean_ctor_set(x_747, 0, x_744);
lean_ctor_set(x_747, 1, x_745);
x_12 = x_747;
goto block_27;
}
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
lean_dec(x_58);
lean_dec(x_30);
x_748 = lean_ctor_get(x_734, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 x_749 = x_734;
} else {
 lean_dec_ref(x_734);
 x_749 = lean_box(0);
}
x_750 = lean_ctor_get(x_735, 0);
lean_inc(x_750);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 x_751 = x_735;
} else {
 lean_dec_ref(x_735);
 x_751 = lean_box(0);
}
lean_ctor_set(x_54, 1, x_750);
lean_ctor_set(x_54, 0, x_686);
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
if (lean_is_scalar(x_732)) {
 x_752 = lean_alloc_ctor(0, 2, 0);
} else {
 x_752 = x_732;
}
lean_ctor_set(x_752, 0, x_1);
lean_ctor_set(x_752, 1, x_28);
if (lean_is_scalar(x_751)) {
 x_753 = lean_alloc_ctor(1, 1, 0);
} else {
 x_753 = x_751;
}
lean_ctor_set(x_753, 0, x_752);
if (lean_is_scalar(x_749)) {
 x_754 = lean_alloc_ctor(0, 2, 0);
} else {
 x_754 = x_749;
}
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_748);
x_12 = x_754;
goto block_27;
}
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_732);
lean_dec(x_686);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_free_object(x_28);
lean_dec(x_30);
x_755 = lean_ctor_get(x_734, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_734, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 x_757 = x_734;
} else {
 lean_dec_ref(x_734);
 x_757 = lean_box(0);
}
if (lean_is_scalar(x_757)) {
 x_758 = lean_alloc_ctor(1, 2, 0);
} else {
 x_758 = x_757;
}
lean_ctor_set(x_758, 0, x_755);
lean_ctor_set(x_758, 1, x_756);
x_12 = x_758;
goto block_27;
}
}
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_dec(x_686);
lean_dec(x_660);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_759 = lean_ctor_get(x_696, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_696, 1);
lean_inc(x_760);
if (lean_is_exclusive(x_696)) {
 lean_ctor_release(x_696, 0);
 lean_ctor_release(x_696, 1);
 x_761 = x_696;
} else {
 lean_dec_ref(x_696);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_761)) {
 x_762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_762 = x_761;
}
lean_ctor_set(x_762, 0, x_759);
lean_ctor_set(x_762, 1, x_760);
x_12 = x_762;
goto block_27;
}
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_686);
lean_dec(x_660);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_763 = lean_ctor_get(x_688, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_688, 1);
lean_inc(x_764);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_765 = x_688;
} else {
 lean_dec_ref(x_688);
 x_765 = lean_box(0);
}
if (lean_is_scalar(x_765)) {
 x_766 = lean_alloc_ctor(1, 2, 0);
} else {
 x_766 = x_765;
}
lean_ctor_set(x_766, 0, x_763);
lean_ctor_set(x_766, 1, x_764);
x_12 = x_766;
goto block_27;
}
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_660);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_767 = lean_ctor_get(x_685, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_685, 1);
lean_inc(x_768);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_769 = x_685;
} else {
 lean_dec_ref(x_685);
 x_769 = lean_box(0);
}
if (lean_is_scalar(x_769)) {
 x_770 = lean_alloc_ctor(1, 2, 0);
} else {
 x_770 = x_769;
}
lean_ctor_set(x_770, 0, x_767);
lean_ctor_set(x_770, 1, x_768);
x_12 = x_770;
goto block_27;
}
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_660);
x_771 = lean_ctor_get(x_658, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_658, 1);
lean_inc(x_772);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_773 = x_658;
} else {
 lean_dec_ref(x_658);
 x_773 = lean_box(0);
}
lean_inc(x_659);
x_774 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_774, 0, x_656);
lean_ctor_set(x_774, 1, x_657);
lean_ctor_set(x_774, 2, x_772);
lean_ctor_set(x_774, 3, x_659);
x_775 = lean_st_ref_take(x_3, x_680);
x_776 = lean_ctor_get(x_775, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_777 = x_775;
} else {
 lean_dec_ref(x_775);
 x_777 = lean_box(0);
}
if (lean_is_scalar(x_773)) {
 x_778 = lean_alloc_ctor(1, 2, 0);
} else {
 x_778 = x_773;
}
lean_ctor_set(x_778, 0, x_774);
lean_ctor_set(x_778, 1, x_59);
if (lean_is_scalar(x_777)) {
 x_779 = lean_alloc_ctor(0, 2, 0);
} else {
 x_779 = x_777;
}
lean_ctor_set(x_779, 0, x_771);
lean_ctor_set(x_779, 1, x_778);
x_780 = lean_st_ref_set(x_3, x_779, x_776);
x_781 = lean_ctor_get(x_780, 1);
lean_inc(x_781);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_782 = x_780;
} else {
 lean_dec_ref(x_780);
 x_782 = lean_box(0);
}
x_783 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_783, 0, x_659);
x_784 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_784, 0, x_783);
if (lean_is_scalar(x_681)) {
 x_785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_785 = x_681;
}
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set(x_785, 1, x_28);
x_786 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_786, 0, x_785);
if (lean_is_scalar(x_782)) {
 x_787 = lean_alloc_ctor(0, 2, 0);
} else {
 x_787 = x_782;
}
lean_ctor_set(x_787, 0, x_786);
lean_ctor_set(x_787, 1, x_781);
x_12 = x_787;
goto block_27;
}
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_681);
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_30);
lean_inc(x_57);
x_788 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_788, 0, x_660);
lean_closure_set(x_788, 1, x_57);
x_789 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_789, 0, x_662);
lean_closure_set(x_789, 1, x_788);
x_790 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_680);
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_790, 1);
lean_inc(x_792);
lean_dec(x_790);
x_793 = lean_ctor_get(x_791, 0);
lean_inc(x_793);
lean_dec(x_791);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_794 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_793, x_789, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_792);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_795 = lean_ctor_get(x_794, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_794, 1);
lean_inc(x_796);
lean_dec(x_794);
x_797 = lean_ctor_get(x_795, 1);
lean_inc(x_797);
lean_dec(x_795);
x_798 = lean_st_ref_take(x_3, x_796);
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_798, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 x_801 = x_798;
} else {
 lean_dec_ref(x_798);
 x_801 = lean_box(0);
}
x_802 = lean_ctor_get(x_799, 1);
lean_inc(x_802);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_803 = x_799;
} else {
 lean_dec_ref(x_799);
 x_803 = lean_box(0);
}
if (lean_is_scalar(x_803)) {
 x_804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_804 = x_803;
}
lean_ctor_set(x_804, 0, x_797);
lean_ctor_set(x_804, 1, x_802);
x_805 = lean_st_ref_set(x_3, x_804, x_800);
x_806 = lean_ctor_get(x_805, 1);
lean_inc(x_806);
if (lean_is_exclusive(x_805)) {
 lean_ctor_release(x_805, 0);
 lean_ctor_release(x_805, 1);
 x_807 = x_805;
} else {
 lean_dec_ref(x_805);
 x_807 = lean_box(0);
}
lean_ctor_set(x_28, 0, x_59);
lean_inc(x_1);
if (lean_is_scalar(x_801)) {
 x_808 = lean_alloc_ctor(0, 2, 0);
} else {
 x_808 = x_801;
}
lean_ctor_set(x_808, 0, x_1);
lean_ctor_set(x_808, 1, x_28);
x_809 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_809, 0, x_808);
if (lean_is_scalar(x_807)) {
 x_810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_810 = x_807;
}
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_806);
x_12 = x_810;
goto block_27;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
x_811 = lean_ctor_get(x_794, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_794, 1);
lean_inc(x_812);
if (lean_is_exclusive(x_794)) {
 lean_ctor_release(x_794, 0);
 lean_ctor_release(x_794, 1);
 x_813 = x_794;
} else {
 lean_dec_ref(x_794);
 x_813 = lean_box(0);
}
if (lean_is_scalar(x_813)) {
 x_814 = lean_alloc_ctor(1, 2, 0);
} else {
 x_814 = x_813;
}
lean_ctor_set(x_814, 0, x_811);
lean_ctor_set(x_814, 1, x_812);
x_12 = x_814;
goto block_27;
}
}
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
lean_dec(x_660);
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_657);
lean_dec(x_656);
lean_dec(x_59);
lean_free_object(x_54);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_28);
lean_dec(x_30);
x_815 = lean_ctor_get(x_668, 0);
lean_inc(x_815);
x_816 = lean_ctor_get(x_668, 1);
lean_inc(x_816);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_817 = x_668;
} else {
 lean_dec_ref(x_668);
 x_817 = lean_box(0);
}
if (lean_is_scalar(x_817)) {
 x_818 = lean_alloc_ctor(1, 2, 0);
} else {
 x_818 = x_817;
}
lean_ctor_set(x_818, 0, x_815);
lean_ctor_set(x_818, 1, x_816);
x_12 = x_818;
goto block_27;
}
}
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_819 = lean_ctor_get(x_54, 0);
x_820 = lean_ctor_get(x_54, 1);
lean_inc(x_820);
lean_inc(x_819);
lean_dec(x_54);
x_821 = lean_ctor_get(x_30, 1);
lean_inc(x_821);
x_822 = lean_ctor_get(x_55, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_55, 1);
lean_inc(x_823);
x_824 = lean_ctor_get(x_55, 2);
lean_inc(x_824);
x_825 = lean_ctor_get(x_55, 3);
lean_inc(x_825);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 x_826 = x_55;
} else {
 lean_dec_ref(x_55);
 x_826 = lean_box(0);
}
x_827 = lean_ctor_get(x_822, 0);
lean_inc(x_827);
lean_inc(x_827);
x_828 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1___boxed), 11, 1);
lean_closure_set(x_828, 0, x_827);
x_829 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_830 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_830, 0, x_829);
lean_closure_set(x_830, 1, x_828);
x_831 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_831, 1);
lean_inc(x_833);
lean_dec(x_831);
x_834 = lean_ctor_get(x_832, 0);
lean_inc(x_834);
lean_dec(x_832);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_835 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_834, x_830, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_833);
if (lean_obj_tag(x_835) == 0)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; uint8_t x_851; 
x_836 = lean_ctor_get(x_835, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_835, 1);
lean_inc(x_837);
lean_dec(x_835);
x_838 = lean_ctor_get(x_836, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_836, 1);
lean_inc(x_839);
lean_dec(x_836);
x_840 = lean_st_ref_take(x_3, x_837);
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_840, 1);
lean_inc(x_842);
lean_dec(x_840);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 x_844 = x_841;
} else {
 lean_dec_ref(x_841);
 x_844 = lean_box(0);
}
if (lean_is_scalar(x_844)) {
 x_845 = lean_alloc_ctor(0, 2, 0);
} else {
 x_845 = x_844;
}
lean_ctor_set(x_845, 0, x_839);
lean_ctor_set(x_845, 1, x_843);
x_846 = lean_st_ref_set(x_3, x_845, x_842);
x_847 = lean_ctor_get(x_846, 1);
lean_inc(x_847);
if (lean_is_exclusive(x_846)) {
 lean_ctor_release(x_846, 0);
 lean_ctor_release(x_846, 1);
 x_848 = x_846;
} else {
 lean_dec_ref(x_846);
 x_848 = lean_box(0);
}
x_849 = lean_ctor_get(x_838, 1);
lean_inc(x_849);
lean_dec(x_838);
x_850 = lean_local_ctx_num_indices(x_849);
x_851 = lean_nat_dec_lt(x_820, x_850);
lean_dec(x_850);
if (x_851 == 0)
{
if (lean_obj_tag(x_824) == 0)
{
lean_object* x_852; 
lean_dec(x_848);
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_822);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_852 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_823, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_847);
if (lean_obj_tag(x_852) == 0)
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_853 = lean_ctor_get(x_852, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_852, 1);
lean_inc(x_854);
lean_dec(x_852);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_853);
lean_inc(x_827);
x_855 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_827, x_853, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_854);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_856 = lean_ctor_get(x_855, 1);
lean_inc(x_856);
lean_dec(x_855);
lean_inc(x_827);
x_857 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_857, 0, x_827);
x_858 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_858, 0, x_829);
lean_closure_set(x_858, 1, x_857);
x_859 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_856);
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_859, 1);
lean_inc(x_861);
lean_dec(x_859);
x_862 = lean_ctor_get(x_860, 0);
lean_inc(x_862);
lean_dec(x_860);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_863 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_862, x_858, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_861);
if (lean_obj_tag(x_863) == 0)
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; uint8_t x_875; 
x_864 = lean_ctor_get(x_863, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_863, 1);
lean_inc(x_865);
lean_dec(x_863);
x_866 = lean_ctor_get(x_864, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_864, 1);
lean_inc(x_867);
lean_dec(x_864);
x_868 = lean_st_ref_take(x_3, x_865);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 x_872 = x_869;
} else {
 lean_dec_ref(x_869);
 x_872 = lean_box(0);
}
if (lean_is_scalar(x_872)) {
 x_873 = lean_alloc_ctor(0, 2, 0);
} else {
 x_873 = x_872;
}
lean_ctor_set(x_873, 0, x_867);
lean_ctor_set(x_873, 1, x_871);
x_874 = lean_st_ref_set(x_3, x_873, x_870);
x_875 = lean_unbox(x_866);
lean_dec(x_866);
if (x_875 == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_853);
lean_dec(x_827);
x_876 = lean_ctor_get(x_874, 1);
lean_inc(x_876);
lean_dec(x_874);
x_877 = lean_st_ref_take(x_3, x_876);
x_878 = lean_ctor_get(x_877, 0);
lean_inc(x_878);
x_879 = lean_ctor_get(x_877, 1);
lean_inc(x_879);
lean_dec(x_877);
x_880 = lean_ctor_get(x_878, 0);
lean_inc(x_880);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_881 = x_878;
} else {
 lean_dec_ref(x_878);
 x_881 = lean_box(0);
}
if (lean_is_scalar(x_881)) {
 x_882 = lean_alloc_ctor(0, 2, 0);
} else {
 x_882 = x_881;
}
lean_ctor_set(x_882, 0, x_880);
lean_ctor_set(x_882, 1, x_821);
x_883 = lean_st_ref_set(x_3, x_882, x_879);
x_884 = lean_ctor_get(x_883, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_883)) {
 lean_ctor_release(x_883, 0);
 lean_ctor_release(x_883, 1);
 x_885 = x_883;
} else {
 lean_dec_ref(x_883);
 x_885 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_886 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_884);
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_886)) {
 lean_ctor_release(x_886, 0);
 lean_ctor_release(x_886, 1);
 x_889 = x_886;
} else {
 lean_dec_ref(x_886);
 x_889 = lean_box(0);
}
x_890 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_890, 0, x_887);
x_891 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_891, 0, x_819);
lean_ctor_set(x_891, 1, x_820);
lean_ctor_set(x_28, 1, x_891);
if (lean_is_scalar(x_885)) {
 x_892 = lean_alloc_ctor(0, 2, 0);
} else {
 x_892 = x_885;
}
lean_ctor_set(x_892, 0, x_890);
lean_ctor_set(x_892, 1, x_28);
x_893 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_893, 0, x_892);
if (lean_is_scalar(x_889)) {
 x_894 = lean_alloc_ctor(0, 2, 0);
} else {
 x_894 = x_889;
}
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_888);
x_12 = x_894;
goto block_27;
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
lean_dec(x_885);
lean_dec(x_820);
lean_dec(x_819);
lean_free_object(x_28);
lean_dec(x_30);
x_895 = lean_ctor_get(x_886, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_886, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_886)) {
 lean_ctor_release(x_886, 0);
 lean_ctor_release(x_886, 1);
 x_897 = x_886;
} else {
 lean_dec_ref(x_886);
 x_897 = lean_box(0);
}
if (lean_is_scalar(x_897)) {
 x_898 = lean_alloc_ctor(1, 2, 0);
} else {
 x_898 = x_897;
}
lean_ctor_set(x_898, 0, x_895);
lean_ctor_set(x_898, 1, x_896);
x_12 = x_898;
goto block_27;
}
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_819);
x_899 = lean_ctor_get(x_874, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 lean_ctor_release(x_874, 1);
 x_900 = x_874;
} else {
 lean_dec_ref(x_874);
 x_900 = lean_box(0);
}
lean_inc(x_853);
x_901 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_901, 0, x_853);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_902 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_827, x_901, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_899);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; 
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; 
lean_dec(x_821);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
lean_dec(x_902);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_853);
x_905 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_853, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_904);
if (lean_obj_tag(x_905) == 0)
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; 
x_906 = lean_ctor_get(x_905, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_907 = x_905;
} else {
 lean_dec_ref(x_905);
 x_907 = lean_box(0);
}
x_908 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_908, 0, x_853);
lean_ctor_set(x_908, 1, x_820);
lean_ctor_set(x_28, 1, x_908);
x_909 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_900)) {
 x_910 = lean_alloc_ctor(0, 2, 0);
} else {
 x_910 = x_900;
}
lean_ctor_set(x_910, 0, x_909);
lean_ctor_set(x_910, 1, x_28);
x_911 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_911, 0, x_910);
if (lean_is_scalar(x_907)) {
 x_912 = lean_alloc_ctor(0, 2, 0);
} else {
 x_912 = x_907;
}
lean_ctor_set(x_912, 0, x_911);
lean_ctor_set(x_912, 1, x_906);
x_12 = x_912;
goto block_27;
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
lean_dec(x_900);
lean_dec(x_853);
lean_dec(x_820);
lean_free_object(x_28);
lean_dec(x_30);
x_913 = lean_ctor_get(x_905, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_905, 1);
lean_inc(x_914);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_915 = x_905;
} else {
 lean_dec_ref(x_905);
 x_915 = lean_box(0);
}
if (lean_is_scalar(x_915)) {
 x_916 = lean_alloc_ctor(1, 2, 0);
} else {
 x_916 = x_915;
}
lean_ctor_set(x_916, 0, x_913);
lean_ctor_set(x_916, 1, x_914);
x_12 = x_916;
goto block_27;
}
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
lean_dec(x_820);
lean_dec(x_30);
x_917 = lean_ctor_get(x_902, 1);
lean_inc(x_917);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_918 = x_902;
} else {
 lean_dec_ref(x_902);
 x_918 = lean_box(0);
}
x_919 = lean_ctor_get(x_903, 0);
lean_inc(x_919);
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 x_920 = x_903;
} else {
 lean_dec_ref(x_903);
 x_920 = lean_box(0);
}
x_921 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_921, 0, x_853);
lean_ctor_set(x_921, 1, x_919);
lean_ctor_set(x_28, 1, x_921);
lean_ctor_set(x_28, 0, x_821);
lean_inc(x_1);
if (lean_is_scalar(x_900)) {
 x_922 = lean_alloc_ctor(0, 2, 0);
} else {
 x_922 = x_900;
}
lean_ctor_set(x_922, 0, x_1);
lean_ctor_set(x_922, 1, x_28);
if (lean_is_scalar(x_920)) {
 x_923 = lean_alloc_ctor(1, 1, 0);
} else {
 x_923 = x_920;
}
lean_ctor_set(x_923, 0, x_922);
if (lean_is_scalar(x_918)) {
 x_924 = lean_alloc_ctor(0, 2, 0);
} else {
 x_924 = x_918;
}
lean_ctor_set(x_924, 0, x_923);
lean_ctor_set(x_924, 1, x_917);
x_12 = x_924;
goto block_27;
}
}
else
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_900);
lean_dec(x_853);
lean_dec(x_821);
lean_dec(x_820);
lean_free_object(x_28);
lean_dec(x_30);
x_925 = lean_ctor_get(x_902, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_902, 1);
lean_inc(x_926);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_927 = x_902;
} else {
 lean_dec_ref(x_902);
 x_927 = lean_box(0);
}
if (lean_is_scalar(x_927)) {
 x_928 = lean_alloc_ctor(1, 2, 0);
} else {
 x_928 = x_927;
}
lean_ctor_set(x_928, 0, x_925);
lean_ctor_set(x_928, 1, x_926);
x_12 = x_928;
goto block_27;
}
}
}
else
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
lean_dec(x_853);
lean_dec(x_827);
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_819);
lean_free_object(x_28);
lean_dec(x_30);
x_929 = lean_ctor_get(x_863, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_863, 1);
lean_inc(x_930);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 x_931 = x_863;
} else {
 lean_dec_ref(x_863);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(1, 2, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_929);
lean_ctor_set(x_932, 1, x_930);
x_12 = x_932;
goto block_27;
}
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; 
lean_dec(x_853);
lean_dec(x_827);
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_819);
lean_free_object(x_28);
lean_dec(x_30);
x_933 = lean_ctor_get(x_855, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_855, 1);
lean_inc(x_934);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_935 = x_855;
} else {
 lean_dec_ref(x_855);
 x_935 = lean_box(0);
}
if (lean_is_scalar(x_935)) {
 x_936 = lean_alloc_ctor(1, 2, 0);
} else {
 x_936 = x_935;
}
lean_ctor_set(x_936, 0, x_933);
lean_ctor_set(x_936, 1, x_934);
x_12 = x_936;
goto block_27;
}
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
lean_dec(x_827);
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_819);
lean_free_object(x_28);
lean_dec(x_30);
x_937 = lean_ctor_get(x_852, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_852, 1);
lean_inc(x_938);
if (lean_is_exclusive(x_852)) {
 lean_ctor_release(x_852, 0);
 lean_ctor_release(x_852, 1);
 x_939 = x_852;
} else {
 lean_dec_ref(x_852);
 x_939 = lean_box(0);
}
if (lean_is_scalar(x_939)) {
 x_940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_940 = x_939;
}
lean_ctor_set(x_940, 0, x_937);
lean_ctor_set(x_940, 1, x_938);
x_12 = x_940;
goto block_27;
}
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
lean_dec(x_827);
x_941 = lean_ctor_get(x_824, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_824, 1);
lean_inc(x_942);
if (lean_is_exclusive(x_824)) {
 lean_ctor_release(x_824, 0);
 lean_ctor_release(x_824, 1);
 x_943 = x_824;
} else {
 lean_dec_ref(x_824);
 x_943 = lean_box(0);
}
lean_inc(x_825);
if (lean_is_scalar(x_826)) {
 x_944 = lean_alloc_ctor(0, 4, 0);
} else {
 x_944 = x_826;
}
lean_ctor_set(x_944, 0, x_822);
lean_ctor_set(x_944, 1, x_823);
lean_ctor_set(x_944, 2, x_942);
lean_ctor_set(x_944, 3, x_825);
x_945 = lean_st_ref_take(x_3, x_847);
x_946 = lean_ctor_get(x_945, 1);
lean_inc(x_946);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_947 = x_945;
} else {
 lean_dec_ref(x_945);
 x_947 = lean_box(0);
}
if (lean_is_scalar(x_943)) {
 x_948 = lean_alloc_ctor(1, 2, 0);
} else {
 x_948 = x_943;
}
lean_ctor_set(x_948, 0, x_944);
lean_ctor_set(x_948, 1, x_821);
if (lean_is_scalar(x_947)) {
 x_949 = lean_alloc_ctor(0, 2, 0);
} else {
 x_949 = x_947;
}
lean_ctor_set(x_949, 0, x_941);
lean_ctor_set(x_949, 1, x_948);
x_950 = lean_st_ref_set(x_3, x_949, x_946);
x_951 = lean_ctor_get(x_950, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_952 = x_950;
} else {
 lean_dec_ref(x_950);
 x_952 = lean_box(0);
}
x_953 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_953, 0, x_825);
x_954 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_954, 0, x_953);
x_955 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_955, 0, x_819);
lean_ctor_set(x_955, 1, x_820);
lean_ctor_set(x_28, 1, x_955);
if (lean_is_scalar(x_848)) {
 x_956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_956 = x_848;
}
lean_ctor_set(x_956, 0, x_954);
lean_ctor_set(x_956, 1, x_28);
x_957 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_957, 0, x_956);
if (lean_is_scalar(x_952)) {
 x_958 = lean_alloc_ctor(0, 2, 0);
} else {
 x_958 = x_952;
}
lean_ctor_set(x_958, 0, x_957);
lean_ctor_set(x_958, 1, x_951);
x_12 = x_958;
goto block_27;
}
}
else
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; 
lean_dec(x_848);
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_30);
lean_inc(x_819);
x_959 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_959, 0, x_827);
lean_closure_set(x_959, 1, x_819);
x_960 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_960, 0, x_829);
lean_closure_set(x_960, 1, x_959);
x_961 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_847);
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
x_964 = lean_ctor_get(x_962, 0);
lean_inc(x_964);
lean_dec(x_962);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_965 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_964, x_960, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_963);
if (lean_obj_tag(x_965) == 0)
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
lean_dec(x_965);
x_968 = lean_ctor_get(x_966, 1);
lean_inc(x_968);
lean_dec(x_966);
x_969 = lean_st_ref_take(x_3, x_967);
x_970 = lean_ctor_get(x_969, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 lean_ctor_release(x_969, 1);
 x_972 = x_969;
} else {
 lean_dec_ref(x_969);
 x_972 = lean_box(0);
}
x_973 = lean_ctor_get(x_970, 1);
lean_inc(x_973);
if (lean_is_exclusive(x_970)) {
 lean_ctor_release(x_970, 0);
 lean_ctor_release(x_970, 1);
 x_974 = x_970;
} else {
 lean_dec_ref(x_970);
 x_974 = lean_box(0);
}
if (lean_is_scalar(x_974)) {
 x_975 = lean_alloc_ctor(0, 2, 0);
} else {
 x_975 = x_974;
}
lean_ctor_set(x_975, 0, x_968);
lean_ctor_set(x_975, 1, x_973);
x_976 = lean_st_ref_set(x_3, x_975, x_971);
x_977 = lean_ctor_get(x_976, 1);
lean_inc(x_977);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_978 = x_976;
} else {
 lean_dec_ref(x_976);
 x_978 = lean_box(0);
}
x_979 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_979, 0, x_819);
lean_ctor_set(x_979, 1, x_820);
lean_ctor_set(x_28, 1, x_979);
lean_ctor_set(x_28, 0, x_821);
lean_inc(x_1);
if (lean_is_scalar(x_972)) {
 x_980 = lean_alloc_ctor(0, 2, 0);
} else {
 x_980 = x_972;
}
lean_ctor_set(x_980, 0, x_1);
lean_ctor_set(x_980, 1, x_28);
x_981 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_981, 0, x_980);
if (lean_is_scalar(x_978)) {
 x_982 = lean_alloc_ctor(0, 2, 0);
} else {
 x_982 = x_978;
}
lean_ctor_set(x_982, 0, x_981);
lean_ctor_set(x_982, 1, x_977);
x_12 = x_982;
goto block_27;
}
else
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_819);
lean_free_object(x_28);
x_983 = lean_ctor_get(x_965, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_965, 1);
lean_inc(x_984);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 x_985 = x_965;
} else {
 lean_dec_ref(x_965);
 x_985 = lean_box(0);
}
if (lean_is_scalar(x_985)) {
 x_986 = lean_alloc_ctor(1, 2, 0);
} else {
 x_986 = x_985;
}
lean_ctor_set(x_986, 0, x_983);
lean_ctor_set(x_986, 1, x_984);
x_12 = x_986;
goto block_27;
}
}
}
else
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; 
lean_dec(x_827);
lean_dec(x_826);
lean_dec(x_825);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_819);
lean_free_object(x_28);
lean_dec(x_30);
x_987 = lean_ctor_get(x_835, 0);
lean_inc(x_987);
x_988 = lean_ctor_get(x_835, 1);
lean_inc(x_988);
if (lean_is_exclusive(x_835)) {
 lean_ctor_release(x_835, 0);
 lean_ctor_release(x_835, 1);
 x_989 = x_835;
} else {
 lean_dec_ref(x_835);
 x_989 = lean_box(0);
}
if (lean_is_scalar(x_989)) {
 x_990 = lean_alloc_ctor(1, 2, 0);
} else {
 x_990 = x_989;
}
lean_ctor_set(x_990, 0, x_987);
lean_ctor_set(x_990, 1, x_988);
x_12 = x_990;
goto block_27;
}
}
}
}
else
{
lean_object* x_991; lean_object* x_992; 
x_991 = lean_ctor_get(x_28, 1);
x_992 = lean_ctor_get(x_28, 0);
lean_inc(x_991);
lean_inc(x_992);
lean_dec(x_28);
if (lean_obj_tag(x_992) == 0)
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_993 = lean_ctor_get(x_991, 0);
lean_inc(x_993);
x_994 = lean_ctor_get(x_991, 1);
lean_inc(x_994);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_995 = x_991;
} else {
 lean_dec_ref(x_991);
 x_995 = lean_box(0);
}
x_996 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_997 = lean_ctor_get(x_996, 1);
lean_inc(x_997);
if (lean_is_exclusive(x_996)) {
 lean_ctor_release(x_996, 0);
 lean_ctor_release(x_996, 1);
 x_998 = x_996;
} else {
 lean_dec_ref(x_996);
 x_998 = lean_box(0);
}
if (lean_is_scalar(x_995)) {
 x_999 = lean_alloc_ctor(0, 2, 0);
} else {
 x_999 = x_995;
}
lean_ctor_set(x_999, 0, x_993);
lean_ctor_set(x_999, 1, x_994);
x_1000 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1000, 0, x_992);
lean_ctor_set(x_1000, 1, x_999);
x_1001 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
x_1002 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1002, 0, x_1001);
lean_ctor_set(x_1002, 1, x_1000);
x_1003 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1003, 0, x_1002);
if (lean_is_scalar(x_998)) {
 x_1004 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1004 = x_998;
}
lean_ctor_set(x_1004, 0, x_1003);
lean_ctor_set(x_1004, 1, x_997);
x_12 = x_1004;
goto block_27;
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1005 = lean_ctor_get(x_992, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_991, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_991, 1);
lean_inc(x_1007);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_1008 = x_991;
} else {
 lean_dec_ref(x_991);
 x_1008 = lean_box(0);
}
x_1009 = lean_ctor_get(x_992, 1);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_1005, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_1005, 1);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_1005, 2);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_1005, 3);
lean_inc(x_1013);
if (lean_is_exclusive(x_1005)) {
 lean_ctor_release(x_1005, 0);
 lean_ctor_release(x_1005, 1);
 lean_ctor_release(x_1005, 2);
 lean_ctor_release(x_1005, 3);
 x_1014 = x_1005;
} else {
 lean_dec_ref(x_1005);
 x_1014 = lean_box(0);
}
x_1015 = lean_ctor_get(x_1010, 0);
lean_inc(x_1015);
lean_inc(x_1015);
x_1016 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1___boxed), 11, 1);
lean_closure_set(x_1016, 0, x_1015);
x_1017 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_1018 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_1018, 0, x_1017);
lean_closure_set(x_1018, 1, x_1016);
x_1019 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_1020 = lean_ctor_get(x_1019, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1019, 1);
lean_inc(x_1021);
lean_dec(x_1019);
x_1022 = lean_ctor_get(x_1020, 0);
lean_inc(x_1022);
lean_dec(x_1020);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1023 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_1022, x_1018, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1021);
if (lean_obj_tag(x_1023) == 0)
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; uint8_t x_1039; 
x_1024 = lean_ctor_get(x_1023, 0);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_1023, 1);
lean_inc(x_1025);
lean_dec(x_1023);
x_1026 = lean_ctor_get(x_1024, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1024, 1);
lean_inc(x_1027);
lean_dec(x_1024);
x_1028 = lean_st_ref_take(x_3, x_1025);
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1028, 1);
lean_inc(x_1030);
lean_dec(x_1028);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1032 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1032 = lean_box(0);
}
if (lean_is_scalar(x_1032)) {
 x_1033 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1033 = x_1032;
}
lean_ctor_set(x_1033, 0, x_1027);
lean_ctor_set(x_1033, 1, x_1031);
x_1034 = lean_st_ref_set(x_3, x_1033, x_1030);
x_1035 = lean_ctor_get(x_1034, 1);
lean_inc(x_1035);
if (lean_is_exclusive(x_1034)) {
 lean_ctor_release(x_1034, 0);
 lean_ctor_release(x_1034, 1);
 x_1036 = x_1034;
} else {
 lean_dec_ref(x_1034);
 x_1036 = lean_box(0);
}
x_1037 = lean_ctor_get(x_1026, 1);
lean_inc(x_1037);
lean_dec(x_1026);
x_1038 = lean_local_ctx_num_indices(x_1037);
x_1039 = lean_nat_dec_lt(x_1007, x_1038);
lean_dec(x_1038);
if (x_1039 == 0)
{
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1040; 
lean_dec(x_1036);
lean_dec(x_1014);
lean_dec(x_1013);
lean_dec(x_1010);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1040 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1(x_1011, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1035);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1041 = lean_ctor_get(x_1040, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
lean_dec(x_1040);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1041);
lean_inc(x_1015);
x_1043 = l_Lean_MVarId_assign___at_Lean_Meta_Grind_mkChoice___spec__1(x_1015, x_1041, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1042);
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1044 = lean_ctor_get(x_1043, 1);
lean_inc(x_1044);
lean_dec(x_1043);
lean_inc(x_1015);
x_1045 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed), 11, 1);
lean_closure_set(x_1045, 0, x_1015);
x_1046 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_1046, 0, x_1017);
lean_closure_set(x_1046, 1, x_1045);
x_1047 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1044);
x_1048 = lean_ctor_get(x_1047, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1047, 1);
lean_inc(x_1049);
lean_dec(x_1047);
x_1050 = lean_ctor_get(x_1048, 0);
lean_inc(x_1050);
lean_dec(x_1048);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1051 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_1050, x_1046, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1049);
if (lean_obj_tag(x_1051) == 0)
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; uint8_t x_1063; 
x_1052 = lean_ctor_get(x_1051, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1051, 1);
lean_inc(x_1053);
lean_dec(x_1051);
x_1054 = lean_ctor_get(x_1052, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1052, 1);
lean_inc(x_1055);
lean_dec(x_1052);
x_1056 = lean_st_ref_take(x_3, x_1053);
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1056, 1);
lean_inc(x_1058);
lean_dec(x_1056);
x_1059 = lean_ctor_get(x_1057, 1);
lean_inc(x_1059);
if (lean_is_exclusive(x_1057)) {
 lean_ctor_release(x_1057, 0);
 lean_ctor_release(x_1057, 1);
 x_1060 = x_1057;
} else {
 lean_dec_ref(x_1057);
 x_1060 = lean_box(0);
}
if (lean_is_scalar(x_1060)) {
 x_1061 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1061 = x_1060;
}
lean_ctor_set(x_1061, 0, x_1055);
lean_ctor_set(x_1061, 1, x_1059);
x_1062 = lean_st_ref_set(x_3, x_1061, x_1058);
x_1063 = lean_unbox(x_1054);
lean_dec(x_1054);
if (x_1063 == 0)
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
lean_dec(x_1041);
lean_dec(x_1015);
x_1064 = lean_ctor_get(x_1062, 1);
lean_inc(x_1064);
lean_dec(x_1062);
x_1065 = lean_st_ref_take(x_3, x_1064);
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
lean_dec(x_1065);
x_1068 = lean_ctor_get(x_1066, 0);
lean_inc(x_1068);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1069 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1069 = lean_box(0);
}
if (lean_is_scalar(x_1069)) {
 x_1070 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1070 = x_1069;
}
lean_ctor_set(x_1070, 0, x_1068);
lean_ctor_set(x_1070, 1, x_1009);
x_1071 = lean_st_ref_set(x_3, x_1070, x_1067);
x_1072 = lean_ctor_get(x_1071, 1);
lean_inc(x_1072);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 x_1073 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1073 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1074 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1072);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1077 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1077 = lean_box(0);
}
x_1078 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1078, 0, x_1075);
if (lean_is_scalar(x_1008)) {
 x_1079 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1079 = x_1008;
}
lean_ctor_set(x_1079, 0, x_1006);
lean_ctor_set(x_1079, 1, x_1007);
x_1080 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1080, 0, x_992);
lean_ctor_set(x_1080, 1, x_1079);
if (lean_is_scalar(x_1073)) {
 x_1081 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1081 = x_1073;
}
lean_ctor_set(x_1081, 0, x_1078);
lean_ctor_set(x_1081, 1, x_1080);
x_1082 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1082, 0, x_1081);
if (lean_is_scalar(x_1077)) {
 x_1083 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1083 = x_1077;
}
lean_ctor_set(x_1083, 0, x_1082);
lean_ctor_set(x_1083, 1, x_1076);
x_12 = x_1083;
goto block_27;
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_1073);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_992);
x_1084 = lean_ctor_get(x_1074, 0);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1074, 1);
lean_inc(x_1085);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1086 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1086 = lean_box(0);
}
if (lean_is_scalar(x_1086)) {
 x_1087 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1087 = x_1086;
}
lean_ctor_set(x_1087, 0, x_1084);
lean_ctor_set(x_1087, 1, x_1085);
x_12 = x_1087;
goto block_27;
}
}
else
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
lean_dec(x_1006);
x_1088 = lean_ctor_get(x_1062, 1);
lean_inc(x_1088);
if (lean_is_exclusive(x_1062)) {
 lean_ctor_release(x_1062, 0);
 lean_ctor_release(x_1062, 1);
 x_1089 = x_1062;
} else {
 lean_dec_ref(x_1062);
 x_1089 = lean_box(0);
}
lean_inc(x_1041);
x_1090 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_1090, 0, x_1041);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1091 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_1015, x_1090, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1088);
if (lean_obj_tag(x_1091) == 0)
{
lean_object* x_1092; 
x_1092 = lean_ctor_get(x_1091, 0);
lean_inc(x_1092);
if (lean_obj_tag(x_1092) == 0)
{
lean_object* x_1093; lean_object* x_1094; 
lean_dec(x_1009);
x_1093 = lean_ctor_get(x_1091, 1);
lean_inc(x_1093);
lean_dec(x_1091);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1041);
x_1094 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_1041, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1093);
if (lean_obj_tag(x_1094) == 0)
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
x_1095 = lean_ctor_get(x_1094, 1);
lean_inc(x_1095);
if (lean_is_exclusive(x_1094)) {
 lean_ctor_release(x_1094, 0);
 lean_ctor_release(x_1094, 1);
 x_1096 = x_1094;
} else {
 lean_dec_ref(x_1094);
 x_1096 = lean_box(0);
}
if (lean_is_scalar(x_1008)) {
 x_1097 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1097 = x_1008;
}
lean_ctor_set(x_1097, 0, x_1041);
lean_ctor_set(x_1097, 1, x_1007);
x_1098 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1098, 0, x_992);
lean_ctor_set(x_1098, 1, x_1097);
x_1099 = l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1;
if (lean_is_scalar(x_1089)) {
 x_1100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1100 = x_1089;
}
lean_ctor_set(x_1100, 0, x_1099);
lean_ctor_set(x_1100, 1, x_1098);
x_1101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1101, 0, x_1100);
if (lean_is_scalar(x_1096)) {
 x_1102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1102 = x_1096;
}
lean_ctor_set(x_1102, 0, x_1101);
lean_ctor_set(x_1102, 1, x_1095);
x_12 = x_1102;
goto block_27;
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
lean_dec(x_1089);
lean_dec(x_1041);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_992);
x_1103 = lean_ctor_get(x_1094, 0);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_1094, 1);
lean_inc(x_1104);
if (lean_is_exclusive(x_1094)) {
 lean_ctor_release(x_1094, 0);
 lean_ctor_release(x_1094, 1);
 x_1105 = x_1094;
} else {
 lean_dec_ref(x_1094);
 x_1105 = lean_box(0);
}
if (lean_is_scalar(x_1105)) {
 x_1106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1106 = x_1105;
}
lean_ctor_set(x_1106, 0, x_1103);
lean_ctor_set(x_1106, 1, x_1104);
x_12 = x_1106;
goto block_27;
}
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
lean_dec(x_1007);
lean_dec(x_992);
x_1107 = lean_ctor_get(x_1091, 1);
lean_inc(x_1107);
if (lean_is_exclusive(x_1091)) {
 lean_ctor_release(x_1091, 0);
 lean_ctor_release(x_1091, 1);
 x_1108 = x_1091;
} else {
 lean_dec_ref(x_1091);
 x_1108 = lean_box(0);
}
x_1109 = lean_ctor_get(x_1092, 0);
lean_inc(x_1109);
if (lean_is_exclusive(x_1092)) {
 lean_ctor_release(x_1092, 0);
 x_1110 = x_1092;
} else {
 lean_dec_ref(x_1092);
 x_1110 = lean_box(0);
}
if (lean_is_scalar(x_1008)) {
 x_1111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1111 = x_1008;
}
lean_ctor_set(x_1111, 0, x_1041);
lean_ctor_set(x_1111, 1, x_1109);
x_1112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1112, 0, x_1009);
lean_ctor_set(x_1112, 1, x_1111);
lean_inc(x_1);
if (lean_is_scalar(x_1089)) {
 x_1113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1113 = x_1089;
}
lean_ctor_set(x_1113, 0, x_1);
lean_ctor_set(x_1113, 1, x_1112);
if (lean_is_scalar(x_1110)) {
 x_1114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1114 = x_1110;
}
lean_ctor_set(x_1114, 0, x_1113);
if (lean_is_scalar(x_1108)) {
 x_1115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1115 = x_1108;
}
lean_ctor_set(x_1115, 0, x_1114);
lean_ctor_set(x_1115, 1, x_1107);
x_12 = x_1115;
goto block_27;
}
}
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
lean_dec(x_1089);
lean_dec(x_1041);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_992);
x_1116 = lean_ctor_get(x_1091, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1091, 1);
lean_inc(x_1117);
if (lean_is_exclusive(x_1091)) {
 lean_ctor_release(x_1091, 0);
 lean_ctor_release(x_1091, 1);
 x_1118 = x_1091;
} else {
 lean_dec_ref(x_1091);
 x_1118 = lean_box(0);
}
if (lean_is_scalar(x_1118)) {
 x_1119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1119 = x_1118;
}
lean_ctor_set(x_1119, 0, x_1116);
lean_ctor_set(x_1119, 1, x_1117);
x_12 = x_1119;
goto block_27;
}
}
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
lean_dec(x_1041);
lean_dec(x_1015);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_992);
x_1120 = lean_ctor_get(x_1051, 0);
lean_inc(x_1120);
x_1121 = lean_ctor_get(x_1051, 1);
lean_inc(x_1121);
if (lean_is_exclusive(x_1051)) {
 lean_ctor_release(x_1051, 0);
 lean_ctor_release(x_1051, 1);
 x_1122 = x_1051;
} else {
 lean_dec_ref(x_1051);
 x_1122 = lean_box(0);
}
if (lean_is_scalar(x_1122)) {
 x_1123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1123 = x_1122;
}
lean_ctor_set(x_1123, 0, x_1120);
lean_ctor_set(x_1123, 1, x_1121);
x_12 = x_1123;
goto block_27;
}
}
else
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
lean_dec(x_1041);
lean_dec(x_1015);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_992);
x_1124 = lean_ctor_get(x_1043, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1043, 1);
lean_inc(x_1125);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1126 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1126 = lean_box(0);
}
if (lean_is_scalar(x_1126)) {
 x_1127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1127 = x_1126;
}
lean_ctor_set(x_1127, 0, x_1124);
lean_ctor_set(x_1127, 1, x_1125);
x_12 = x_1127;
goto block_27;
}
}
else
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
lean_dec(x_1015);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_992);
x_1128 = lean_ctor_get(x_1040, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1040, 1);
lean_inc(x_1129);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1130 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1130 = lean_box(0);
}
if (lean_is_scalar(x_1130)) {
 x_1131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1131 = x_1130;
}
lean_ctor_set(x_1131, 0, x_1128);
lean_ctor_set(x_1131, 1, x_1129);
x_12 = x_1131;
goto block_27;
}
}
else
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
lean_dec(x_1015);
x_1132 = lean_ctor_get(x_1012, 0);
lean_inc(x_1132);
x_1133 = lean_ctor_get(x_1012, 1);
lean_inc(x_1133);
if (lean_is_exclusive(x_1012)) {
 lean_ctor_release(x_1012, 0);
 lean_ctor_release(x_1012, 1);
 x_1134 = x_1012;
} else {
 lean_dec_ref(x_1012);
 x_1134 = lean_box(0);
}
lean_inc(x_1013);
if (lean_is_scalar(x_1014)) {
 x_1135 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1135 = x_1014;
}
lean_ctor_set(x_1135, 0, x_1010);
lean_ctor_set(x_1135, 1, x_1011);
lean_ctor_set(x_1135, 2, x_1133);
lean_ctor_set(x_1135, 3, x_1013);
x_1136 = lean_st_ref_take(x_3, x_1035);
x_1137 = lean_ctor_get(x_1136, 1);
lean_inc(x_1137);
if (lean_is_exclusive(x_1136)) {
 lean_ctor_release(x_1136, 0);
 lean_ctor_release(x_1136, 1);
 x_1138 = x_1136;
} else {
 lean_dec_ref(x_1136);
 x_1138 = lean_box(0);
}
if (lean_is_scalar(x_1134)) {
 x_1139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1139 = x_1134;
}
lean_ctor_set(x_1139, 0, x_1135);
lean_ctor_set(x_1139, 1, x_1009);
if (lean_is_scalar(x_1138)) {
 x_1140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1140 = x_1138;
}
lean_ctor_set(x_1140, 0, x_1132);
lean_ctor_set(x_1140, 1, x_1139);
x_1141 = lean_st_ref_set(x_3, x_1140, x_1137);
x_1142 = lean_ctor_get(x_1141, 1);
lean_inc(x_1142);
if (lean_is_exclusive(x_1141)) {
 lean_ctor_release(x_1141, 0);
 lean_ctor_release(x_1141, 1);
 x_1143 = x_1141;
} else {
 lean_dec_ref(x_1141);
 x_1143 = lean_box(0);
}
x_1144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1144, 0, x_1013);
x_1145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1145, 0, x_1144);
if (lean_is_scalar(x_1008)) {
 x_1146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1146 = x_1008;
}
lean_ctor_set(x_1146, 0, x_1006);
lean_ctor_set(x_1146, 1, x_1007);
x_1147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1147, 0, x_992);
lean_ctor_set(x_1147, 1, x_1146);
if (lean_is_scalar(x_1036)) {
 x_1148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1148 = x_1036;
}
lean_ctor_set(x_1148, 0, x_1145);
lean_ctor_set(x_1148, 1, x_1147);
x_1149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1149, 0, x_1148);
if (lean_is_scalar(x_1143)) {
 x_1150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1150 = x_1143;
}
lean_ctor_set(x_1150, 0, x_1149);
lean_ctor_set(x_1150, 1, x_1142);
x_12 = x_1150;
goto block_27;
}
}
else
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
lean_dec(x_1036);
lean_dec(x_1014);
lean_dec(x_1013);
lean_dec(x_1012);
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_992);
lean_inc(x_1006);
x_1151 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lambda__1___boxed), 12, 2);
lean_closure_set(x_1151, 0, x_1015);
lean_closure_set(x_1151, 1, x_1006);
x_1152 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_1152, 0, x_1017);
lean_closure_set(x_1152, 1, x_1151);
x_1153 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1035);
x_1154 = lean_ctor_get(x_1153, 0);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1153, 1);
lean_inc(x_1155);
lean_dec(x_1153);
x_1156 = lean_ctor_get(x_1154, 0);
lean_inc(x_1156);
lean_dec(x_1154);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1157 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_1156, x_1152, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_1155);
if (lean_obj_tag(x_1157) == 0)
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
x_1158 = lean_ctor_get(x_1157, 0);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_1157, 1);
lean_inc(x_1159);
lean_dec(x_1157);
x_1160 = lean_ctor_get(x_1158, 1);
lean_inc(x_1160);
lean_dec(x_1158);
x_1161 = lean_st_ref_take(x_3, x_1159);
x_1162 = lean_ctor_get(x_1161, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_1161, 1);
lean_inc(x_1163);
if (lean_is_exclusive(x_1161)) {
 lean_ctor_release(x_1161, 0);
 lean_ctor_release(x_1161, 1);
 x_1164 = x_1161;
} else {
 lean_dec_ref(x_1161);
 x_1164 = lean_box(0);
}
x_1165 = lean_ctor_get(x_1162, 1);
lean_inc(x_1165);
if (lean_is_exclusive(x_1162)) {
 lean_ctor_release(x_1162, 0);
 lean_ctor_release(x_1162, 1);
 x_1166 = x_1162;
} else {
 lean_dec_ref(x_1162);
 x_1166 = lean_box(0);
}
if (lean_is_scalar(x_1166)) {
 x_1167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1167 = x_1166;
}
lean_ctor_set(x_1167, 0, x_1160);
lean_ctor_set(x_1167, 1, x_1165);
x_1168 = lean_st_ref_set(x_3, x_1167, x_1163);
x_1169 = lean_ctor_get(x_1168, 1);
lean_inc(x_1169);
if (lean_is_exclusive(x_1168)) {
 lean_ctor_release(x_1168, 0);
 lean_ctor_release(x_1168, 1);
 x_1170 = x_1168;
} else {
 lean_dec_ref(x_1168);
 x_1170 = lean_box(0);
}
if (lean_is_scalar(x_1008)) {
 x_1171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1171 = x_1008;
}
lean_ctor_set(x_1171, 0, x_1006);
lean_ctor_set(x_1171, 1, x_1007);
x_1172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1172, 0, x_1009);
lean_ctor_set(x_1172, 1, x_1171);
lean_inc(x_1);
if (lean_is_scalar(x_1164)) {
 x_1173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1173 = x_1164;
}
lean_ctor_set(x_1173, 0, x_1);
lean_ctor_set(x_1173, 1, x_1172);
x_1174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1174, 0, x_1173);
if (lean_is_scalar(x_1170)) {
 x_1175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1175 = x_1170;
}
lean_ctor_set(x_1175, 0, x_1174);
lean_ctor_set(x_1175, 1, x_1169);
x_12 = x_1175;
goto block_27;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_1006);
x_1176 = lean_ctor_get(x_1157, 0);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1157, 1);
lean_inc(x_1177);
if (lean_is_exclusive(x_1157)) {
 lean_ctor_release(x_1157, 0);
 lean_ctor_release(x_1157, 1);
 x_1178 = x_1157;
} else {
 lean_dec_ref(x_1157);
 x_1178 = lean_box(0);
}
if (lean_is_scalar(x_1178)) {
 x_1179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1179 = x_1178;
}
lean_ctor_set(x_1179, 0, x_1176);
lean_ctor_set(x_1179, 1, x_1177);
x_12 = x_1179;
goto block_27;
}
}
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
lean_dec(x_1015);
lean_dec(x_1014);
lean_dec(x_1013);
lean_dec(x_1012);
lean_dec(x_1011);
lean_dec(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_1006);
lean_dec(x_992);
x_1180 = lean_ctor_get(x_1023, 0);
lean_inc(x_1180);
x_1181 = lean_ctor_get(x_1023, 1);
lean_inc(x_1181);
if (lean_is_exclusive(x_1023)) {
 lean_ctor_release(x_1023, 0);
 lean_ctor_release(x_1023, 1);
 x_1182 = x_1023;
} else {
 lean_dec_ref(x_1023);
 x_1182 = lean_box(0);
}
if (lean_is_scalar(x_1182)) {
 x_1183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1183 = x_1182;
}
lean_ctor_set(x_1183, 0, x_1180);
lean_ctor_set(x_1183, 1, x_1181);
x_12 = x_1183;
goto block_27;
}
}
}
block_27:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_2 = x_21;
x_11 = x_20;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f(x_1, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_15, x_19);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_18);
lean_ctor_set(x_20, 0, x_13);
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
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_13);
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f(x_1, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_30, x_34);
lean_dec(x_30);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_43 = x_32;
} else {
 lean_dec_ref(x_32);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.nextGoal\?", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_mkChoice___closed__6;
x_2 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__1;
x_3 = lean_unsigned_to_nat(221u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__2;
x_12 = l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("goal.inconsistent\n  ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_mkChoice___closed__3;
x_2 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_mkChoice___closed__6;
x_2 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__1;
x_3 = lean_unsigned_to_nat(176u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*16);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__3;
x_18 = l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_nextGoal_x3f___lambda__1___boxed), 11, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = l_Lean_Meta_Grind_liftGoalM___rarg___closed__1;
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Grind_liftGoalM___spec__2___rarg), 11, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
x_24 = l_Lean_Meta_Grind_getGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_27, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
x_34 = lean_st_ref_take(x_3, x_30);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
lean_ctor_set(x_36, 0, x_33);
x_40 = lean_st_ref_set(x_3, x_36, x_38);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_34);
lean_free_object(x_29);
lean_dec(x_20);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_40, 1);
x_45 = lean_ctor_get(x_40, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_32, 0);
lean_inc(x_46);
lean_dec(x_32);
lean_inc(x_46);
x_47 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_47, 0, x_46);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_48 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_20, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_free_object(x_40);
lean_free_object(x_34);
lean_free_object(x_29);
lean_dec(x_1);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_dec(x_48);
x_63 = lean_ctor_get(x_49, 0);
lean_inc(x_63);
lean_dec(x_49);
x_64 = lean_box(0);
lean_ctor_set(x_40, 1, x_63);
lean_ctor_set(x_40, 0, x_46);
lean_ctor_set(x_34, 1, x_40);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_29, 1, x_34);
lean_ctor_set(x_29, 0, x_64);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_65 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3(x_64, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__4;
x_70 = lean_box(0);
x_71 = lean_apply_10(x_69, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_68);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_65);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_65, 0);
lean_dec(x_73);
x_74 = lean_ctor_get(x_67, 0);
lean_inc(x_74);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_74);
return x_65;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_65, 1);
lean_inc(x_75);
lean_dec(x_65);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
lean_dec(x_67);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_65);
if (x_78 == 0)
{
return x_65;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_65, 0);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_65);
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
lean_dec(x_46);
lean_free_object(x_40);
lean_free_object(x_34);
lean_free_object(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_48);
if (x_82 == 0)
{
return x_48;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_48, 0);
x_84 = lean_ctor_get(x_48, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_48);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_40, 1);
lean_inc(x_86);
lean_dec(x_40);
x_87 = lean_ctor_get(x_32, 0);
lean_inc(x_87);
lean_dec(x_32);
lean_inc(x_87);
x_88 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_88, 0, x_87);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_89 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_20, x_88, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_86);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_free_object(x_34);
lean_free_object(x_29);
lean_dec(x_1);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
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
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_89, 1);
lean_inc(x_101);
lean_dec(x_89);
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
lean_dec(x_90);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_87);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_34, 1, x_104);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_29, 1, x_34);
lean_ctor_set(x_29, 0, x_103);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_105 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3(x_103, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_101);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__4;
x_110 = lean_box(0);
x_111 = lean_apply_10(x_109, x_110, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_113 = x_105;
} else {
 lean_dec_ref(x_105);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_107, 0);
lean_inc(x_114);
lean_dec(x_107);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_116 = lean_ctor_get(x_105, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_118 = x_105;
} else {
 lean_dec_ref(x_105);
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
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_87);
lean_free_object(x_34);
lean_free_object(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_120 = lean_ctor_get(x_89, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_89, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_122 = x_89;
} else {
 lean_dec_ref(x_89);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_34, 1);
x_125 = lean_ctor_get(x_36, 1);
lean_inc(x_125);
lean_dec(x_36);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_33);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_st_ref_set(x_3, x_126, x_124);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_free_object(x_34);
lean_free_object(x_29);
lean_dec(x_20);
lean_dec(x_1);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_128);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_32, 0);
lean_inc(x_132);
lean_dec(x_32);
lean_inc(x_132);
x_133 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_133, 0, x_132);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_134 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_20, x_133, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_130);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_131);
lean_free_object(x_34);
lean_free_object(x_29);
lean_dec(x_1);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_132, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
x_140 = lean_box(0);
if (lean_is_scalar(x_139)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_139;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_138);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_137, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_137, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_144 = x_137;
} else {
 lean_dec_ref(x_137);
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
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_134, 1);
lean_inc(x_146);
lean_dec(x_134);
x_147 = lean_ctor_get(x_135, 0);
lean_inc(x_147);
lean_dec(x_135);
x_148 = lean_box(0);
if (lean_is_scalar(x_131)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_131;
}
lean_ctor_set(x_149, 0, x_132);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_34, 1, x_149);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_29, 1, x_34);
lean_ctor_set(x_29, 0, x_148);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_150 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3(x_148, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_146);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec(x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__4;
x_155 = lean_box(0);
x_156 = lean_apply_10(x_154, x_155, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_153);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = lean_ctor_get(x_150, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_158 = x_150;
} else {
 lean_dec_ref(x_150);
 x_158 = lean_box(0);
}
x_159 = lean_ctor_get(x_152, 0);
lean_inc(x_159);
lean_dec(x_152);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_161 = lean_ctor_get(x_150, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_150, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_163 = x_150;
} else {
 lean_dec_ref(x_150);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_132);
lean_dec(x_131);
lean_free_object(x_34);
lean_free_object(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_165 = lean_ctor_get(x_134, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_134, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_167 = x_134;
} else {
 lean_dec_ref(x_134);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_169 = lean_ctor_get(x_34, 0);
x_170 = lean_ctor_get(x_34, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_34);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_33);
lean_ctor_set(x_173, 1, x_171);
x_174 = lean_st_ref_set(x_3, x_173, x_170);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_free_object(x_29);
lean_dec(x_20);
lean_dec(x_1);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_175);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_178 = x_174;
} else {
 lean_dec_ref(x_174);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_32, 0);
lean_inc(x_179);
lean_dec(x_32);
lean_inc(x_179);
x_180 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_180, 0, x_179);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_181 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_20, x_180, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_177);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_178);
lean_free_object(x_29);
lean_dec(x_1);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_179, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_186 = x_184;
} else {
 lean_dec_ref(x_184);
 x_186 = lean_box(0);
}
x_187 = lean_box(0);
if (lean_is_scalar(x_186)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_186;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_185);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_184, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_191 = x_184;
} else {
 lean_dec_ref(x_184);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_193 = lean_ctor_get(x_181, 1);
lean_inc(x_193);
lean_dec(x_181);
x_194 = lean_ctor_get(x_182, 0);
lean_inc(x_194);
lean_dec(x_182);
x_195 = lean_box(0);
if (lean_is_scalar(x_178)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_178;
}
lean_ctor_set(x_196, 0, x_179);
lean_ctor_set(x_196, 1, x_194);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_1);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set(x_29, 1, x_197);
lean_ctor_set(x_29, 0, x_195);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_198 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3(x_195, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_193);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
lean_dec(x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec(x_198);
x_202 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__4;
x_203 = lean_box(0);
x_204 = lean_apply_10(x_202, x_203, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_201);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_205 = lean_ctor_get(x_198, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_206 = x_198;
} else {
 lean_dec_ref(x_198);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_200, 0);
lean_inc(x_207);
lean_dec(x_200);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_209 = lean_ctor_get(x_198, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_198, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_211 = x_198;
} else {
 lean_dec_ref(x_198);
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
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_179);
lean_dec(x_178);
lean_free_object(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_213 = lean_ctor_get(x_181, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_181, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_215 = x_181;
} else {
 lean_dec_ref(x_181);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_217 = lean_ctor_get(x_29, 0);
x_218 = lean_ctor_get(x_29, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_29);
x_219 = lean_st_ref_take(x_3, x_30);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_224 = x_220;
} else {
 lean_dec_ref(x_220);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_218);
lean_ctor_set(x_225, 1, x_223);
x_226 = lean_st_ref_set(x_3, x_225, x_221);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_222);
lean_dec(x_20);
lean_dec(x_1);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_228 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_227);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_230 = x_226;
} else {
 lean_dec_ref(x_226);
 x_230 = lean_box(0);
}
x_231 = lean_ctor_get(x_217, 0);
lean_inc(x_231);
lean_dec(x_217);
lean_inc(x_231);
x_232 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3___lambda__1), 10, 1);
lean_closure_set(x_232, 0, x_231);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_233 = l_Lean_MVarId_withContext___at_Lean_Meta_Grind_withCurrGoalContext___spec__1___rarg(x_20, x_232, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_229);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_230);
lean_dec(x_222);
lean_dec(x_1);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_231, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_235);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
x_239 = lean_box(0);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_236, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_243 = x_236;
} else {
 lean_dec_ref(x_236);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_245 = lean_ctor_get(x_233, 1);
lean_inc(x_245);
lean_dec(x_233);
x_246 = lean_ctor_get(x_234, 0);
lean_inc(x_246);
lean_dec(x_234);
x_247 = lean_box(0);
if (lean_is_scalar(x_230)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_230;
}
lean_ctor_set(x_248, 0, x_231);
lean_ctor_set(x_248, 1, x_246);
if (lean_is_scalar(x_222)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_222;
}
lean_ctor_set(x_249, 0, x_1);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_249);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_251 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___at_Lean_Meta_Grind_nextGoal_x3f___spec__3(x_247, x_250, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_245);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec(x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__4;
x_256 = lean_box(0);
x_257 = lean_apply_10(x_255, x_256, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_254);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_260 = lean_ctor_get(x_253, 0);
lean_inc(x_260);
lean_dec(x_253);
if (lean_is_scalar(x_259)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_259;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_258);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_262 = lean_ctor_get(x_251, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_251, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_264 = x_251;
} else {
 lean_dec_ref(x_251);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_222);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_266 = lean_ctor_get(x_233, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_233, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_268 = x_233;
} else {
 lean_dec_ref(x_233);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
}
}
else
{
uint8_t x_270; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_28);
if (x_270 == 0)
{
return x_28;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_28, 0);
x_272 = lean_ctor_get(x_28, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_28);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___boxed), 11, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Grind_nextGoal_x3f___closed__1;
x_16 = l_List_isEmpty___rarg(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_10);
x_17 = lean_box(0);
x_18 = lean_apply_11(x_15, x_14, x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Grind_nextGoal_x3f___closed__1;
x_24 = l_List_isEmpty___rarg(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = lean_apply_11(x_23, x_22, x_25, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Loop_forIn_loop___at_Lean_Meta_Grind_nextGoal_x3f___spec__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_nextGoal_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_SearchM(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_ForEachExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedChoice___closed__1 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__1);
l_Lean_Meta_Grind_instInhabitedChoice___closed__2 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__2);
l_Lean_Meta_Grind_instInhabitedChoice___closed__3 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__3);
l_Lean_Meta_Grind_instInhabitedChoice___closed__4 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__4);
l_Lean_Meta_Grind_instInhabitedChoice___closed__5 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__5);
l_Lean_Meta_Grind_instInhabitedChoice___closed__6 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__6();
l_Lean_Meta_Grind_instInhabitedChoice___closed__7 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__7);
l_Lean_Meta_Grind_instInhabitedChoice___closed__8 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__8);
l_Lean_Meta_Grind_instInhabitedChoice___closed__9 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__9);
l_Lean_Meta_Grind_instInhabitedChoice___closed__10 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__10);
l_Lean_Meta_Grind_instInhabitedChoice___closed__11 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__11);
l_Lean_Meta_Grind_instInhabitedChoice___closed__12 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__12);
l_Lean_Meta_Grind_instInhabitedChoice___closed__13 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__13);
l_Lean_Meta_Grind_instInhabitedChoice___closed__14 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__14);
l_Lean_Meta_Grind_instInhabitedChoice___closed__15 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__15);
l_Lean_Meta_Grind_instInhabitedChoice___closed__16 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__16);
l_Lean_Meta_Grind_instInhabitedChoice___closed__17 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__17);
l_Lean_Meta_Grind_instInhabitedChoice___closed__18 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__18();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__18);
l_Lean_Meta_Grind_instInhabitedChoice___closed__19 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__19();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__19);
l_Lean_Meta_Grind_instInhabitedChoice___closed__20 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__20();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__20);
l_Lean_Meta_Grind_instInhabitedChoice___closed__21 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__21();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__21);
l_Lean_Meta_Grind_instInhabitedChoice___closed__22 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__22();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__22);
l_Lean_Meta_Grind_instInhabitedChoice___closed__23 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__23();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__23);
l_Lean_Meta_Grind_instInhabitedChoice___closed__24 = _init_l_Lean_Meta_Grind_instInhabitedChoice___closed__24();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice___closed__24);
l_Lean_Meta_Grind_instInhabitedChoice = _init_l_Lean_Meta_Grind_instInhabitedChoice();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice);
l_Lean_Meta_Grind_liftGoalM___rarg___closed__1 = _init_l_Lean_Meta_Grind_liftGoalM___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___rarg___closed__1);
l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__1 = _init_l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__1);
l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__2 = _init_l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__2();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__2);
l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__3 = _init_l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__3();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__3);
l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__4 = _init_l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__4();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__4);
l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__5 = _init_l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__5();
lean_mark_persistent(l_panic___at_Lean_Meta_Grind_mkChoice___spec__2___closed__5);
l_Lean_Meta_Grind_mkChoice___closed__1 = _init_l_Lean_Meta_Grind_mkChoice___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__1);
l_Lean_Meta_Grind_mkChoice___closed__2 = _init_l_Lean_Meta_Grind_mkChoice___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__2);
l_Lean_Meta_Grind_mkChoice___closed__3 = _init_l_Lean_Meta_Grind_mkChoice___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__3);
l_Lean_Meta_Grind_mkChoice___closed__4 = _init_l_Lean_Meta_Grind_mkChoice___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__4);
l_Lean_Meta_Grind_mkChoice___closed__5 = _init_l_Lean_Meta_Grind_mkChoice___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__5);
l_Lean_Meta_Grind_mkChoice___closed__6 = _init_l_Lean_Meta_Grind_mkChoice___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__6);
l_Lean_Meta_Grind_mkChoice___closed__7 = _init_l_Lean_Meta_Grind_mkChoice___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__7);
l_Lean_Meta_Grind_mkChoice___closed__8 = _init_l_Lean_Meta_Grind_mkChoice___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__8);
l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__1 = _init_l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__1);
l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__2 = _init_l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__2);
l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__3 = _init_l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_mkAuxMVarForCurrGoal___closed__3);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1);
l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1 = _init_l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__1___closed__1);
l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2___closed__1 = _init_l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___spec__2___closed__1);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lambda__1___closed__5);
l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__1 = _init_l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__1);
l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__2 = _init_l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__2();
lean_mark_persistent(l_Lean_instantiateMVars___at_Lean_Meta_Grind_nextGoal_x3f___spec__1___closed__2);
l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__1);
l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___lambda__2___closed__2);
l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__1 = _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__1);
l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__2 = _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__2);
l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__3 = _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__3);
l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__4 = _init_l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___lambda__3___closed__4);
l_Lean_Meta_Grind_nextGoal_x3f___closed__1 = _init_l_Lean_Meta_Grind_nextGoal_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
