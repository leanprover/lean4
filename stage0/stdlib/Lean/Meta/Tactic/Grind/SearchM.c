// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SearchM
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Util.ForEachExpr
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_cases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedChoice;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedProofTrace;
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__0;
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__13;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_instantiate_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_mkChoice_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__2;
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__1;
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice_default___closed__5;
static lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_solver_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_instantiate_elim___redArg(lean_object*, lean_object*);
lean_object* l_List_getLast___redArg(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_done_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__8;
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_solver_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedProofStep;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assignFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedChoice_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__12;
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice_default___closed__4;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedGoal_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedProofStep_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_State_ctorIdx___boxed(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_cases_elim___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_lookahead_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_ctorIdx(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_sep_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_lookahead_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__4;
static lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__10;
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__0;
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Choice_ctorIdx(lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__4;
static lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Choice_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__0;
uint8_t l_Lean_Expr_isFalse(lean_object*);
static lean_object* l_Lean_Meta_Grind_instMonadLiftGoalMSearchM___closed__0;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedProofStep_default___closed__0;
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkChoice___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static size_t l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal___redArg(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_instMonadControlReaderT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_sep_elim___redArg(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_mbtc_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedProofTrace_default;
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_State_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__3;
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_local_ctx_num_indices(lean_object*);
static lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_mkChoice_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__4;
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_instInhabitedChoice_default___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instMonadLiftGoalMSearchM;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_nextGoal_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_mbtc_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_ProofStep_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
case 3:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_ProofStep_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_solver_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_solver_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_lookahead_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_lookahead_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_mbtc_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_mbtc_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_instantiate_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofStep_instantiate_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_ProofStep_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedProofStep_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedProofStep_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedProofStep_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedProofStep() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedProofStep_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_ProofTrace_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_ProofTrace_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_ProofTrace_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_done_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_ProofTrace_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_done_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_ProofTrace_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_sep_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_ProofTrace_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_sep_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_ProofTrace_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_cases_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_ProofTrace_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ProofTrace_cases_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_ProofTrace_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedProofTrace_default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedProofTrace() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Choice_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Choice_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Choice_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoal_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice_default___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_instInhabitedChoice_default___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Grind_instInhabitedChoice_default___closed__4;
x_3 = lean_box(0);
x_4 = l_Lean_Meta_Grind_instInhabitedChoice_default___closed__3;
x_5 = l_Lean_Meta_Grind_instInhabitedChoice_default___closed__0;
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice_default___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedChoice() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedChoice_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_State_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_State_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_SearchM_State_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getGoal___redArg(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_getGoal___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_1);
x_7 = lean_st_ref_set(x_2, x_4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_st_ref_set(x_2, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_setGoal___redArg(x_1, x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_setGoal___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_setGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_setGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadControlReaderT(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1;
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 2);
x_16 = lean_ctor_get(x_12, 3);
x_17 = lean_ctor_get(x_12, 4);
x_18 = lean_ctor_get(x_12, 1);
lean_dec(x_18);
x_19 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_20 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_14);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_15);
lean_ctor_set(x_12, 4, x_24);
lean_ctor_set(x_12, 3, x_25);
lean_ctor_set(x_12, 2, x_26);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_20);
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_37 = lean_ctor_get(x_30, 1);
lean_dec(x_37);
x_38 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_39 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_34);
lean_ctor_set(x_30, 4, x_43);
lean_ctor_set(x_30, 3, x_44);
lean_ctor_set(x_30, 2, x_45);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set(x_28, 1, x_39);
x_46 = l_ReaderT_instMonad___redArg(x_28);
x_47 = l_ReaderT_instMonad___redArg(x_46);
x_48 = l_ReaderT_instMonad___redArg(x_47);
x_49 = l_ReaderT_instMonad___redArg(x_48);
x_50 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = lean_ctor_get(x_11, 1);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 2);
x_57 = lean_ctor_get(x_52, 3);
x_58 = lean_ctor_get(x_52, 4);
x_59 = lean_ctor_get(x_52, 1);
lean_dec(x_59);
lean_inc_ref(x_55);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_60, 0, x_55);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_55);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_58);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_64, 0, x_57);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_65, 0, x_56);
lean_ctor_set(x_52, 4, x_63);
lean_ctor_set(x_52, 3, x_64);
lean_ctor_set(x_52, 2, x_65);
lean_ctor_set(x_52, 1, x_19);
lean_ctor_set(x_52, 0, x_62);
lean_ctor_set(x_11, 1, x_20);
x_66 = l_ReaderT_instMonad___redArg(x_11);
x_67 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_67, 0, lean_box(0));
lean_closure_set(x_67, 1, lean_box(0));
lean_closure_set(x_67, 2, x_66);
x_68 = l_instMonadControlTOfPure___redArg(x_67);
lean_inc_ref(x_68);
x_69 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_69, 0, x_50);
lean_closure_set(x_69, 1, x_68);
x_70 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_70, 0, x_50);
lean_closure_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_inc_ref(x_71);
x_72 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_72, 0, x_50);
lean_closure_set(x_72, 1, x_71);
x_73 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_73, 0, x_50);
lean_closure_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_inc_ref(x_74);
x_75 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_75, 0, x_50);
lean_closure_set(x_75, 1, x_74);
x_76 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_76, 0, x_50);
lean_closure_set(x_76, 1, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_inc_ref(x_77);
x_78 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_78, 0, x_50);
lean_closure_set(x_78, 1, x_77);
x_79 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_79, 0, x_50);
lean_closure_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_MVarId_withContext___redArg(x_80, x_49, x_83, x_1);
x_85 = lean_apply_9(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_86 = lean_ctor_get(x_52, 0);
x_87 = lean_ctor_get(x_52, 2);
x_88 = lean_ctor_get(x_52, 3);
x_89 = lean_ctor_get(x_52, 4);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_52);
lean_inc_ref(x_86);
x_90 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_90, 0, x_86);
x_91 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_91, 0, x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_93, 0, x_89);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_94, 0, x_88);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_95, 0, x_87);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_19);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_94);
lean_ctor_set(x_96, 4, x_93);
lean_ctor_set(x_11, 1, x_20);
lean_ctor_set(x_11, 0, x_96);
x_97 = l_ReaderT_instMonad___redArg(x_11);
x_98 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_98, 0, lean_box(0));
lean_closure_set(x_98, 1, lean_box(0));
lean_closure_set(x_98, 2, x_97);
x_99 = l_instMonadControlTOfPure___redArg(x_98);
lean_inc_ref(x_99);
x_100 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_100, 0, x_50);
lean_closure_set(x_100, 1, x_99);
x_101 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_101, 0, x_50);
lean_closure_set(x_101, 1, x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_inc_ref(x_102);
x_103 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_103, 0, x_50);
lean_closure_set(x_103, 1, x_102);
x_104 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_104, 0, x_50);
lean_closure_set(x_104, 1, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_inc_ref(x_105);
x_106 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_106, 0, x_50);
lean_closure_set(x_106, 1, x_105);
x_107 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_107, 0, x_50);
lean_closure_set(x_107, 1, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_inc_ref(x_108);
x_109 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_109, 0, x_50);
lean_closure_set(x_109, 1, x_108);
x_110 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_110, 0, x_50);
lean_closure_set(x_110, 1, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lean_MVarId_withContext___redArg(x_111, x_49, x_114, x_1);
x_116 = lean_apply_9(x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_117 = lean_ctor_get(x_11, 0);
lean_inc(x_117);
lean_dec(x_11);
x_118 = lean_ctor_get(x_117, 0);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_117, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_117, 4);
lean_inc(x_121);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 x_122 = x_117;
} else {
 lean_dec_ref(x_117);
 x_122 = lean_box(0);
}
lean_inc_ref(x_118);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_123, 0, x_118);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_124, 0, x_118);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_126, 0, x_121);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_127, 0, x_120);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_128, 0, x_119);
if (lean_is_scalar(x_122)) {
 x_129 = lean_alloc_ctor(0, 5, 0);
} else {
 x_129 = x_122;
}
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_19);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_127);
lean_ctor_set(x_129, 4, x_126);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_20);
x_131 = l_ReaderT_instMonad___redArg(x_130);
x_132 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_132, 0, lean_box(0));
lean_closure_set(x_132, 1, lean_box(0));
lean_closure_set(x_132, 2, x_131);
x_133 = l_instMonadControlTOfPure___redArg(x_132);
lean_inc_ref(x_133);
x_134 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_134, 0, x_50);
lean_closure_set(x_134, 1, x_133);
x_135 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_135, 0, x_50);
lean_closure_set(x_135, 1, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_inc_ref(x_136);
x_137 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_137, 0, x_50);
lean_closure_set(x_137, 1, x_136);
x_138 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_138, 0, x_50);
lean_closure_set(x_138, 1, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_inc_ref(x_139);
x_140 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_140, 0, x_50);
lean_closure_set(x_140, 1, x_139);
x_141 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_141, 0, x_50);
lean_closure_set(x_141, 1, x_139);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_inc_ref(x_142);
x_143 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_143, 0, x_50);
lean_closure_set(x_143, 1, x_142);
x_144 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_144, 0, x_50);
lean_closure_set(x_144, 1, x_142);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lean_MVarId_withContext___redArg(x_145, x_49, x_148, x_1);
x_150 = lean_apply_9(x_149, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_151 = lean_ctor_get(x_30, 0);
x_152 = lean_ctor_get(x_30, 2);
x_153 = lean_ctor_get(x_30, 3);
x_154 = lean_ctor_get(x_30, 4);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_30);
x_155 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_156 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_151);
x_157 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_157, 0, x_151);
x_158 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_158, 0, x_151);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_160, 0, x_154);
x_161 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_161, 0, x_153);
x_162 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_162, 0, x_152);
x_163 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_162);
lean_ctor_set(x_163, 3, x_161);
lean_ctor_set(x_163, 4, x_160);
lean_ctor_set(x_28, 1, x_156);
lean_ctor_set(x_28, 0, x_163);
x_164 = l_ReaderT_instMonad___redArg(x_28);
x_165 = l_ReaderT_instMonad___redArg(x_164);
x_166 = l_ReaderT_instMonad___redArg(x_165);
x_167 = l_ReaderT_instMonad___redArg(x_166);
x_168 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_169 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_169);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_170 = x_11;
} else {
 lean_dec_ref(x_11);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_169, 0);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_169, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 4);
lean_inc(x_174);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 x_175 = x_169;
} else {
 lean_dec_ref(x_169);
 x_175 = lean_box(0);
}
lean_inc_ref(x_171);
x_176 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_176, 0, x_171);
x_177 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_177, 0, x_171);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_179, 0, x_174);
x_180 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_180, 0, x_173);
x_181 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_181, 0, x_172);
if (lean_is_scalar(x_175)) {
 x_182 = lean_alloc_ctor(0, 5, 0);
} else {
 x_182 = x_175;
}
lean_ctor_set(x_182, 0, x_178);
lean_ctor_set(x_182, 1, x_19);
lean_ctor_set(x_182, 2, x_181);
lean_ctor_set(x_182, 3, x_180);
lean_ctor_set(x_182, 4, x_179);
if (lean_is_scalar(x_170)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_170;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_20);
x_184 = l_ReaderT_instMonad___redArg(x_183);
x_185 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_185, 0, lean_box(0));
lean_closure_set(x_185, 1, lean_box(0));
lean_closure_set(x_185, 2, x_184);
x_186 = l_instMonadControlTOfPure___redArg(x_185);
lean_inc_ref(x_186);
x_187 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_187, 0, x_168);
lean_closure_set(x_187, 1, x_186);
x_188 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_188, 0, x_168);
lean_closure_set(x_188, 1, x_186);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_inc_ref(x_189);
x_190 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_190, 0, x_168);
lean_closure_set(x_190, 1, x_189);
x_191 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_191, 0, x_168);
lean_closure_set(x_191, 1, x_189);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
lean_inc_ref(x_192);
x_193 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_193, 0, x_168);
lean_closure_set(x_193, 1, x_192);
x_194 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_194, 0, x_168);
lean_closure_set(x_194, 1, x_192);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
lean_inc_ref(x_195);
x_196 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_196, 0, x_168);
lean_closure_set(x_196, 1, x_195);
x_197 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_197, 0, x_168);
lean_closure_set(x_197, 1, x_195);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
lean_dec_ref(x_199);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_202 = l_Lean_MVarId_withContext___redArg(x_198, x_167, x_201, x_1);
x_203 = lean_apply_9(x_202, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_204 = lean_ctor_get(x_28, 0);
lean_inc(x_204);
lean_dec(x_28);
x_205 = lean_ctor_get(x_204, 0);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_204, 2);
lean_inc(x_206);
x_207 = lean_ctor_get(x_204, 3);
lean_inc(x_207);
x_208 = lean_ctor_get(x_204, 4);
lean_inc(x_208);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 lean_ctor_release(x_204, 2);
 lean_ctor_release(x_204, 3);
 lean_ctor_release(x_204, 4);
 x_209 = x_204;
} else {
 lean_dec_ref(x_204);
 x_209 = lean_box(0);
}
x_210 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_211 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_205);
x_212 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_212, 0, x_205);
x_213 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_213, 0, x_205);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_215, 0, x_208);
x_216 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_216, 0, x_207);
x_217 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_217, 0, x_206);
if (lean_is_scalar(x_209)) {
 x_218 = lean_alloc_ctor(0, 5, 0);
} else {
 x_218 = x_209;
}
lean_ctor_set(x_218, 0, x_214);
lean_ctor_set(x_218, 1, x_210);
lean_ctor_set(x_218, 2, x_217);
lean_ctor_set(x_218, 3, x_216);
lean_ctor_set(x_218, 4, x_215);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_211);
x_220 = l_ReaderT_instMonad___redArg(x_219);
x_221 = l_ReaderT_instMonad___redArg(x_220);
x_222 = l_ReaderT_instMonad___redArg(x_221);
x_223 = l_ReaderT_instMonad___redArg(x_222);
x_224 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_225 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_225);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_226 = x_11;
} else {
 lean_dec_ref(x_11);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_225, 0);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_225, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_225, 3);
lean_inc(x_229);
x_230 = lean_ctor_get(x_225, 4);
lean_inc(x_230);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 lean_ctor_release(x_225, 2);
 lean_ctor_release(x_225, 3);
 lean_ctor_release(x_225, 4);
 x_231 = x_225;
} else {
 lean_dec_ref(x_225);
 x_231 = lean_box(0);
}
lean_inc_ref(x_227);
x_232 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_232, 0, x_227);
x_233 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_233, 0, x_227);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_235, 0, x_230);
x_236 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_236, 0, x_229);
x_237 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_237, 0, x_228);
if (lean_is_scalar(x_231)) {
 x_238 = lean_alloc_ctor(0, 5, 0);
} else {
 x_238 = x_231;
}
lean_ctor_set(x_238, 0, x_234);
lean_ctor_set(x_238, 1, x_19);
lean_ctor_set(x_238, 2, x_237);
lean_ctor_set(x_238, 3, x_236);
lean_ctor_set(x_238, 4, x_235);
if (lean_is_scalar(x_226)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_226;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_20);
x_240 = l_ReaderT_instMonad___redArg(x_239);
x_241 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_241, 0, lean_box(0));
lean_closure_set(x_241, 1, lean_box(0));
lean_closure_set(x_241, 2, x_240);
x_242 = l_instMonadControlTOfPure___redArg(x_241);
lean_inc_ref(x_242);
x_243 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_243, 0, x_224);
lean_closure_set(x_243, 1, x_242);
x_244 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_244, 0, x_224);
lean_closure_set(x_244, 1, x_242);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
lean_inc_ref(x_245);
x_246 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_246, 0, x_224);
lean_closure_set(x_246, 1, x_245);
x_247 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_247, 0, x_224);
lean_closure_set(x_247, 1, x_245);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
lean_inc_ref(x_248);
x_249 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_249, 0, x_224);
lean_closure_set(x_249, 1, x_248);
x_250 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_250, 0, x_224);
lean_closure_set(x_250, 1, x_248);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
lean_inc_ref(x_251);
x_252 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_252, 0, x_224);
lean_closure_set(x_252, 1, x_251);
x_253 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_253, 0, x_224);
lean_closure_set(x_253, 1, x_251);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec_ref(x_255);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec(x_256);
x_258 = l_Lean_MVarId_withContext___redArg(x_254, x_223, x_257, x_1);
x_259 = lean_apply_9(x_258, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_260 = lean_ctor_get(x_12, 0);
x_261 = lean_ctor_get(x_12, 2);
x_262 = lean_ctor_get(x_12, 3);
x_263 = lean_ctor_get(x_12, 4);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_12);
x_264 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_265 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_260);
x_266 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_266, 0, x_260);
x_267 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_267, 0, x_260);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_269, 0, x_263);
x_270 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_270, 0, x_262);
x_271 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_271, 0, x_261);
x_272 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_272, 0, x_268);
lean_ctor_set(x_272, 1, x_264);
lean_ctor_set(x_272, 2, x_271);
lean_ctor_set(x_272, 3, x_270);
lean_ctor_set(x_272, 4, x_269);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_265);
x_274 = l_ReaderT_instMonad___redArg(x_273);
x_275 = lean_ctor_get(x_274, 0);
lean_inc_ref(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_275, 0);
lean_inc_ref(x_277);
x_278 = lean_ctor_get(x_275, 2);
lean_inc(x_278);
x_279 = lean_ctor_get(x_275, 3);
lean_inc(x_279);
x_280 = lean_ctor_get(x_275, 4);
lean_inc(x_280);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 lean_ctor_release(x_275, 2);
 lean_ctor_release(x_275, 3);
 lean_ctor_release(x_275, 4);
 x_281 = x_275;
} else {
 lean_dec_ref(x_275);
 x_281 = lean_box(0);
}
x_282 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_283 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_277);
x_284 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_284, 0, x_277);
x_285 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_285, 0, x_277);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_287, 0, x_280);
x_288 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_288, 0, x_279);
x_289 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_289, 0, x_278);
if (lean_is_scalar(x_281)) {
 x_290 = lean_alloc_ctor(0, 5, 0);
} else {
 x_290 = x_281;
}
lean_ctor_set(x_290, 0, x_286);
lean_ctor_set(x_290, 1, x_282);
lean_ctor_set(x_290, 2, x_289);
lean_ctor_set(x_290, 3, x_288);
lean_ctor_set(x_290, 4, x_287);
if (lean_is_scalar(x_276)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_276;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_283);
x_292 = l_ReaderT_instMonad___redArg(x_291);
x_293 = l_ReaderT_instMonad___redArg(x_292);
x_294 = l_ReaderT_instMonad___redArg(x_293);
x_295 = l_ReaderT_instMonad___redArg(x_294);
x_296 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_297 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_297);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_298 = x_11;
} else {
 lean_dec_ref(x_11);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_297, 0);
lean_inc_ref(x_299);
x_300 = lean_ctor_get(x_297, 2);
lean_inc(x_300);
x_301 = lean_ctor_get(x_297, 3);
lean_inc(x_301);
x_302 = lean_ctor_get(x_297, 4);
lean_inc(x_302);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 lean_ctor_release(x_297, 2);
 lean_ctor_release(x_297, 3);
 lean_ctor_release(x_297, 4);
 x_303 = x_297;
} else {
 lean_dec_ref(x_297);
 x_303 = lean_box(0);
}
lean_inc_ref(x_299);
x_304 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_304, 0, x_299);
x_305 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_305, 0, x_299);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_307, 0, x_302);
x_308 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_308, 0, x_301);
x_309 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_309, 0, x_300);
if (lean_is_scalar(x_303)) {
 x_310 = lean_alloc_ctor(0, 5, 0);
} else {
 x_310 = x_303;
}
lean_ctor_set(x_310, 0, x_306);
lean_ctor_set(x_310, 1, x_264);
lean_ctor_set(x_310, 2, x_309);
lean_ctor_set(x_310, 3, x_308);
lean_ctor_set(x_310, 4, x_307);
if (lean_is_scalar(x_298)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_298;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_265);
x_312 = l_ReaderT_instMonad___redArg(x_311);
x_313 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_313, 0, lean_box(0));
lean_closure_set(x_313, 1, lean_box(0));
lean_closure_set(x_313, 2, x_312);
x_314 = l_instMonadControlTOfPure___redArg(x_313);
lean_inc_ref(x_314);
x_315 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_315, 0, x_296);
lean_closure_set(x_315, 1, x_314);
x_316 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_316, 0, x_296);
lean_closure_set(x_316, 1, x_314);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
lean_inc_ref(x_317);
x_318 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_318, 0, x_296);
lean_closure_set(x_318, 1, x_317);
x_319 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_319, 0, x_296);
lean_closure_set(x_319, 1, x_317);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
lean_inc_ref(x_320);
x_321 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_321, 0, x_296);
lean_closure_set(x_321, 1, x_320);
x_322 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_322, 0, x_296);
lean_closure_set(x_322, 1, x_320);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
lean_inc_ref(x_323);
x_324 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_324, 0, x_296);
lean_closure_set(x_324, 1, x_323);
x_325 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_325, 0, x_296);
lean_closure_set(x_325, 1, x_323);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
x_327 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
lean_dec_ref(x_327);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
lean_dec(x_328);
x_330 = l_Lean_MVarId_withContext___redArg(x_326, x_295, x_329, x_1);
x_331 = lean_apply_9(x_330, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_331;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1;
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 2);
x_17 = lean_ctor_get(x_13, 3);
x_18 = lean_ctor_get(x_13, 4);
x_19 = lean_ctor_get(x_13, 1);
lean_dec(x_19);
x_20 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_21 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_16);
lean_ctor_set(x_13, 4, x_25);
lean_ctor_set(x_13, 3, x_26);
lean_ctor_set(x_13, 2, x_27);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_21);
x_29 = l_ReaderT_instMonad___redArg(x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_38 = lean_ctor_get(x_31, 1);
lean_dec(x_38);
x_39 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_40 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_36);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_35);
lean_ctor_set(x_31, 4, x_44);
lean_ctor_set(x_31, 3, x_45);
lean_ctor_set(x_31, 2, x_46);
lean_ctor_set(x_31, 1, x_39);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_29, 1, x_40);
x_47 = l_ReaderT_instMonad___redArg(x_29);
x_48 = l_ReaderT_instMonad___redArg(x_47);
x_49 = l_ReaderT_instMonad___redArg(x_48);
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_ctor_get(x_53, 2);
x_58 = lean_ctor_get(x_53, 3);
x_59 = lean_ctor_get(x_53, 4);
x_60 = lean_ctor_get(x_53, 1);
lean_dec(x_60);
lean_inc_ref(x_56);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_61, 0, x_56);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_62, 0, x_56);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_64, 0, x_59);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_65, 0, x_58);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_66, 0, x_57);
lean_ctor_set(x_53, 4, x_64);
lean_ctor_set(x_53, 3, x_65);
lean_ctor_set(x_53, 2, x_66);
lean_ctor_set(x_53, 1, x_20);
lean_ctor_set(x_53, 0, x_63);
lean_ctor_set(x_12, 1, x_21);
x_67 = l_ReaderT_instMonad___redArg(x_12);
x_68 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_68, 0, lean_box(0));
lean_closure_set(x_68, 1, lean_box(0));
lean_closure_set(x_68, 2, x_67);
x_69 = l_instMonadControlTOfPure___redArg(x_68);
lean_inc_ref(x_69);
x_70 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_70, 0, x_51);
lean_closure_set(x_70, 1, x_69);
x_71 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_71, 0, x_51);
lean_closure_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_inc_ref(x_72);
x_73 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_73, 0, x_51);
lean_closure_set(x_73, 1, x_72);
x_74 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_74, 0, x_51);
lean_closure_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc_ref(x_75);
x_76 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_76, 0, x_51);
lean_closure_set(x_76, 1, x_75);
x_77 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_77, 0, x_51);
lean_closure_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
lean_inc_ref(x_78);
x_79 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_79, 0, x_51);
lean_closure_set(x_79, 1, x_78);
x_80 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_80, 0, x_51);
lean_closure_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Lean_MVarId_withContext___redArg(x_81, x_50, x_84, x_2);
x_86 = lean_apply_9(x_85, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_87 = lean_ctor_get(x_53, 0);
x_88 = lean_ctor_get(x_53, 2);
x_89 = lean_ctor_get(x_53, 3);
x_90 = lean_ctor_get(x_53, 4);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_53);
lean_inc_ref(x_87);
x_91 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_91, 0, x_87);
x_92 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_92, 0, x_87);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_94, 0, x_90);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_95, 0, x_89);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_96, 0, x_88);
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_20);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_95);
lean_ctor_set(x_97, 4, x_94);
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_97);
x_98 = l_ReaderT_instMonad___redArg(x_12);
x_99 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_99, 0, lean_box(0));
lean_closure_set(x_99, 1, lean_box(0));
lean_closure_set(x_99, 2, x_98);
x_100 = l_instMonadControlTOfPure___redArg(x_99);
lean_inc_ref(x_100);
x_101 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_101, 0, x_51);
lean_closure_set(x_101, 1, x_100);
x_102 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_102, 0, x_51);
lean_closure_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_inc_ref(x_103);
x_104 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_104, 0, x_51);
lean_closure_set(x_104, 1, x_103);
x_105 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_105, 0, x_51);
lean_closure_set(x_105, 1, x_103);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_inc_ref(x_106);
x_107 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_107, 0, x_51);
lean_closure_set(x_107, 1, x_106);
x_108 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_108, 0, x_51);
lean_closure_set(x_108, 1, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
lean_inc_ref(x_109);
x_110 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_110, 0, x_51);
lean_closure_set(x_110, 1, x_109);
x_111 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_111, 0, x_51);
lean_closure_set(x_111, 1, x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Lean_MVarId_withContext___redArg(x_112, x_50, x_115, x_2);
x_117 = lean_apply_9(x_116, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_118 = lean_ctor_get(x_12, 0);
lean_inc(x_118);
lean_dec(x_12);
x_119 = lean_ctor_get(x_118, 0);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_118, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 4);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
lean_inc_ref(x_119);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_124, 0, x_119);
x_125 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_125, 0, x_119);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_127, 0, x_122);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_128, 0, x_121);
x_129 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_129, 0, x_120);
if (lean_is_scalar(x_123)) {
 x_130 = lean_alloc_ctor(0, 5, 0);
} else {
 x_130 = x_123;
}
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_20);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_128);
lean_ctor_set(x_130, 4, x_127);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_21);
x_132 = l_ReaderT_instMonad___redArg(x_131);
x_133 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_133, 0, lean_box(0));
lean_closure_set(x_133, 1, lean_box(0));
lean_closure_set(x_133, 2, x_132);
x_134 = l_instMonadControlTOfPure___redArg(x_133);
lean_inc_ref(x_134);
x_135 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_135, 0, x_51);
lean_closure_set(x_135, 1, x_134);
x_136 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_136, 0, x_51);
lean_closure_set(x_136, 1, x_134);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_inc_ref(x_137);
x_138 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_138, 0, x_51);
lean_closure_set(x_138, 1, x_137);
x_139 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_139, 0, x_51);
lean_closure_set(x_139, 1, x_137);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_inc_ref(x_140);
x_141 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_141, 0, x_51);
lean_closure_set(x_141, 1, x_140);
x_142 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_142, 0, x_51);
lean_closure_set(x_142, 1, x_140);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_inc_ref(x_143);
x_144 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_144, 0, x_51);
lean_closure_set(x_144, 1, x_143);
x_145 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_145, 0, x_51);
lean_closure_set(x_145, 1, x_143);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l_Lean_MVarId_withContext___redArg(x_146, x_50, x_149, x_2);
x_151 = lean_apply_9(x_150, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_152 = lean_ctor_get(x_31, 0);
x_153 = lean_ctor_get(x_31, 2);
x_154 = lean_ctor_get(x_31, 3);
x_155 = lean_ctor_get(x_31, 4);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_31);
x_156 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_157 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_152);
x_158 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_158, 0, x_152);
x_159 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_159, 0, x_152);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_161, 0, x_155);
x_162 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_162, 0, x_154);
x_163 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_163, 0, x_153);
x_164 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_164, 0, x_160);
lean_ctor_set(x_164, 1, x_156);
lean_ctor_set(x_164, 2, x_163);
lean_ctor_set(x_164, 3, x_162);
lean_ctor_set(x_164, 4, x_161);
lean_ctor_set(x_29, 1, x_157);
lean_ctor_set(x_29, 0, x_164);
x_165 = l_ReaderT_instMonad___redArg(x_29);
x_166 = l_ReaderT_instMonad___redArg(x_165);
x_167 = l_ReaderT_instMonad___redArg(x_166);
x_168 = l_ReaderT_instMonad___redArg(x_167);
x_169 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_170 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_170);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_171 = x_12;
} else {
 lean_dec_ref(x_12);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_170, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_170, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 4);
lean_inc(x_175);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 x_176 = x_170;
} else {
 lean_dec_ref(x_170);
 x_176 = lean_box(0);
}
lean_inc_ref(x_172);
x_177 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_177, 0, x_172);
x_178 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_178, 0, x_172);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_180, 0, x_175);
x_181 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_181, 0, x_174);
x_182 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_182, 0, x_173);
if (lean_is_scalar(x_176)) {
 x_183 = lean_alloc_ctor(0, 5, 0);
} else {
 x_183 = x_176;
}
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_20);
lean_ctor_set(x_183, 2, x_182);
lean_ctor_set(x_183, 3, x_181);
lean_ctor_set(x_183, 4, x_180);
if (lean_is_scalar(x_171)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_171;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_21);
x_185 = l_ReaderT_instMonad___redArg(x_184);
x_186 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_186, 0, lean_box(0));
lean_closure_set(x_186, 1, lean_box(0));
lean_closure_set(x_186, 2, x_185);
x_187 = l_instMonadControlTOfPure___redArg(x_186);
lean_inc_ref(x_187);
x_188 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_188, 0, x_169);
lean_closure_set(x_188, 1, x_187);
x_189 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_189, 0, x_169);
lean_closure_set(x_189, 1, x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_inc_ref(x_190);
x_191 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_191, 0, x_169);
lean_closure_set(x_191, 1, x_190);
x_192 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_192, 0, x_169);
lean_closure_set(x_192, 1, x_190);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
lean_inc_ref(x_193);
x_194 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_194, 0, x_169);
lean_closure_set(x_194, 1, x_193);
x_195 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_195, 0, x_169);
lean_closure_set(x_195, 1, x_193);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
lean_inc_ref(x_196);
x_197 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_197, 0, x_169);
lean_closure_set(x_197, 1, x_196);
x_198 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_198, 0, x_169);
lean_closure_set(x_198, 1, x_196);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec(x_201);
x_203 = l_Lean_MVarId_withContext___redArg(x_199, x_168, x_202, x_2);
x_204 = lean_apply_9(x_203, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_205 = lean_ctor_get(x_29, 0);
lean_inc(x_205);
lean_dec(x_29);
x_206 = lean_ctor_get(x_205, 0);
lean_inc_ref(x_206);
x_207 = lean_ctor_get(x_205, 2);
lean_inc(x_207);
x_208 = lean_ctor_get(x_205, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_205, 4);
lean_inc(x_209);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 lean_ctor_release(x_205, 4);
 x_210 = x_205;
} else {
 lean_dec_ref(x_205);
 x_210 = lean_box(0);
}
x_211 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_212 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_206);
x_213 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_213, 0, x_206);
x_214 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_214, 0, x_206);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_216, 0, x_209);
x_217 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_217, 0, x_208);
x_218 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_218, 0, x_207);
if (lean_is_scalar(x_210)) {
 x_219 = lean_alloc_ctor(0, 5, 0);
} else {
 x_219 = x_210;
}
lean_ctor_set(x_219, 0, x_215);
lean_ctor_set(x_219, 1, x_211);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_217);
lean_ctor_set(x_219, 4, x_216);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_212);
x_221 = l_ReaderT_instMonad___redArg(x_220);
x_222 = l_ReaderT_instMonad___redArg(x_221);
x_223 = l_ReaderT_instMonad___redArg(x_222);
x_224 = l_ReaderT_instMonad___redArg(x_223);
x_225 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_226 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_226);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_227 = x_12;
} else {
 lean_dec_ref(x_12);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_226, 0);
lean_inc_ref(x_228);
x_229 = lean_ctor_get(x_226, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_226, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_226, 4);
lean_inc(x_231);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 lean_ctor_release(x_226, 3);
 lean_ctor_release(x_226, 4);
 x_232 = x_226;
} else {
 lean_dec_ref(x_226);
 x_232 = lean_box(0);
}
lean_inc_ref(x_228);
x_233 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_233, 0, x_228);
x_234 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_234, 0, x_228);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_236, 0, x_231);
x_237 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_237, 0, x_230);
x_238 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_238, 0, x_229);
if (lean_is_scalar(x_232)) {
 x_239 = lean_alloc_ctor(0, 5, 0);
} else {
 x_239 = x_232;
}
lean_ctor_set(x_239, 0, x_235);
lean_ctor_set(x_239, 1, x_20);
lean_ctor_set(x_239, 2, x_238);
lean_ctor_set(x_239, 3, x_237);
lean_ctor_set(x_239, 4, x_236);
if (lean_is_scalar(x_227)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_227;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_21);
x_241 = l_ReaderT_instMonad___redArg(x_240);
x_242 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_242, 0, lean_box(0));
lean_closure_set(x_242, 1, lean_box(0));
lean_closure_set(x_242, 2, x_241);
x_243 = l_instMonadControlTOfPure___redArg(x_242);
lean_inc_ref(x_243);
x_244 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_244, 0, x_225);
lean_closure_set(x_244, 1, x_243);
x_245 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_245, 0, x_225);
lean_closure_set(x_245, 1, x_243);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
lean_inc_ref(x_246);
x_247 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_247, 0, x_225);
lean_closure_set(x_247, 1, x_246);
x_248 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_248, 0, x_225);
lean_closure_set(x_248, 1, x_246);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
lean_inc_ref(x_249);
x_250 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_250, 0, x_225);
lean_closure_set(x_250, 1, x_249);
x_251 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_251, 0, x_225);
lean_closure_set(x_251, 1, x_249);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
lean_inc_ref(x_252);
x_253 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_253, 0, x_225);
lean_closure_set(x_253, 1, x_252);
x_254 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_254, 0, x_225);
lean_closure_set(x_254, 1, x_252);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
x_256 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec(x_257);
x_259 = l_Lean_MVarId_withContext___redArg(x_255, x_224, x_258, x_2);
x_260 = lean_apply_9(x_259, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_261 = lean_ctor_get(x_13, 0);
x_262 = lean_ctor_get(x_13, 2);
x_263 = lean_ctor_get(x_13, 3);
x_264 = lean_ctor_get(x_13, 4);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_13);
x_265 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_266 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_261);
x_267 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_267, 0, x_261);
x_268 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_268, 0, x_261);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_270, 0, x_264);
x_271 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_271, 0, x_263);
x_272 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_272, 0, x_262);
x_273 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_273, 0, x_269);
lean_ctor_set(x_273, 1, x_265);
lean_ctor_set(x_273, 2, x_272);
lean_ctor_set(x_273, 3, x_271);
lean_ctor_set(x_273, 4, x_270);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_266);
x_275 = l_ReaderT_instMonad___redArg(x_274);
x_276 = lean_ctor_get(x_275, 0);
lean_inc_ref(x_276);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_277 = x_275;
} else {
 lean_dec_ref(x_275);
 x_277 = lean_box(0);
}
x_278 = lean_ctor_get(x_276, 0);
lean_inc_ref(x_278);
x_279 = lean_ctor_get(x_276, 2);
lean_inc(x_279);
x_280 = lean_ctor_get(x_276, 3);
lean_inc(x_280);
x_281 = lean_ctor_get(x_276, 4);
lean_inc(x_281);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 lean_ctor_release(x_276, 2);
 lean_ctor_release(x_276, 3);
 lean_ctor_release(x_276, 4);
 x_282 = x_276;
} else {
 lean_dec_ref(x_276);
 x_282 = lean_box(0);
}
x_283 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_284 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_278);
x_285 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_285, 0, x_278);
x_286 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_286, 0, x_278);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_288, 0, x_281);
x_289 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_289, 0, x_280);
x_290 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_290, 0, x_279);
if (lean_is_scalar(x_282)) {
 x_291 = lean_alloc_ctor(0, 5, 0);
} else {
 x_291 = x_282;
}
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_283);
lean_ctor_set(x_291, 2, x_290);
lean_ctor_set(x_291, 3, x_289);
lean_ctor_set(x_291, 4, x_288);
if (lean_is_scalar(x_277)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_277;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_284);
x_293 = l_ReaderT_instMonad___redArg(x_292);
x_294 = l_ReaderT_instMonad___redArg(x_293);
x_295 = l_ReaderT_instMonad___redArg(x_294);
x_296 = l_ReaderT_instMonad___redArg(x_295);
x_297 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_298 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_298);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_299 = x_12;
} else {
 lean_dec_ref(x_12);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_298, 0);
lean_inc_ref(x_300);
x_301 = lean_ctor_get(x_298, 2);
lean_inc(x_301);
x_302 = lean_ctor_get(x_298, 3);
lean_inc(x_302);
x_303 = lean_ctor_get(x_298, 4);
lean_inc(x_303);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 lean_ctor_release(x_298, 2);
 lean_ctor_release(x_298, 3);
 lean_ctor_release(x_298, 4);
 x_304 = x_298;
} else {
 lean_dec_ref(x_298);
 x_304 = lean_box(0);
}
lean_inc_ref(x_300);
x_305 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_305, 0, x_300);
x_306 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_306, 0, x_300);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_308, 0, x_303);
x_309 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_309, 0, x_302);
x_310 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_310, 0, x_301);
if (lean_is_scalar(x_304)) {
 x_311 = lean_alloc_ctor(0, 5, 0);
} else {
 x_311 = x_304;
}
lean_ctor_set(x_311, 0, x_307);
lean_ctor_set(x_311, 1, x_265);
lean_ctor_set(x_311, 2, x_310);
lean_ctor_set(x_311, 3, x_309);
lean_ctor_set(x_311, 4, x_308);
if (lean_is_scalar(x_299)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_299;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_266);
x_313 = l_ReaderT_instMonad___redArg(x_312);
x_314 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_314, 0, lean_box(0));
lean_closure_set(x_314, 1, lean_box(0));
lean_closure_set(x_314, 2, x_313);
x_315 = l_instMonadControlTOfPure___redArg(x_314);
lean_inc_ref(x_315);
x_316 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_316, 0, x_297);
lean_closure_set(x_316, 1, x_315);
x_317 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_317, 0, x_297);
lean_closure_set(x_317, 1, x_315);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
lean_inc_ref(x_318);
x_319 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_319, 0, x_297);
lean_closure_set(x_319, 1, x_318);
x_320 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_320, 0, x_297);
lean_closure_set(x_320, 1, x_318);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
lean_inc_ref(x_321);
x_322 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_322, 0, x_297);
lean_closure_set(x_322, 1, x_321);
x_323 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_323, 0, x_297);
lean_closure_set(x_323, 1, x_321);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
lean_inc_ref(x_324);
x_325 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_325, 0, x_297);
lean_closure_set(x_325, 1, x_324);
x_326 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_326, 0, x_297);
lean_closure_set(x_326, 1, x_324);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
x_328 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
lean_dec_ref(x_328);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
lean_dec(x_329);
x_331 = l_Lean_MVarId_withContext___redArg(x_327, x_296, x_330, x_2);
x_332 = lean_apply_9(x_331, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_332;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_withCurrGoalContext___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_withCurrGoalContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_withCurrGoalContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
x_13 = lean_st_mk_ref(x_12);
lean_inc(x_13);
x_14 = lean_apply_9(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftBaseIOEIO___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftT___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__4;
x_2 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__5;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__3;
x_2 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__6;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__2;
x_2 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__7;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__1;
x_2 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__8;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__0;
x_2 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__9;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__1;
x_2 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__10;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__0;
x_2 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__11;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__0;
x_2 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__12;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__13;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1;
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 2);
x_16 = lean_ctor_get(x_12, 3);
x_17 = lean_ctor_get(x_12, 4);
x_18 = lean_ctor_get(x_12, 1);
lean_dec(x_18);
x_19 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_20 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_14);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_16);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_26, 0, x_15);
lean_ctor_set(x_12, 4, x_24);
lean_ctor_set(x_12, 3, x_25);
lean_ctor_set(x_12, 2, x_26);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_20);
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 2);
x_35 = lean_ctor_get(x_30, 3);
x_36 = lean_ctor_get(x_30, 4);
x_37 = lean_ctor_get(x_30, 1);
lean_dec(x_37);
x_38 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_39 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_36);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_35);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_34);
lean_ctor_set(x_30, 4, x_43);
lean_ctor_set(x_30, 3, x_44);
lean_ctor_set(x_30, 2, x_45);
lean_ctor_set(x_30, 1, x_38);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set(x_28, 1, x_39);
x_46 = l_ReaderT_instMonad___redArg(x_28);
x_47 = l_ReaderT_instMonad___redArg(x_46);
x_48 = l_ReaderT_instMonad___redArg(x_47);
lean_inc_ref(x_48);
x_49 = l_ReaderT_instMonad___redArg(x_48);
x_50 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = lean_ctor_get(x_11, 1);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 2);
x_57 = lean_ctor_get(x_52, 3);
x_58 = lean_ctor_get(x_52, 4);
x_59 = lean_ctor_get(x_52, 1);
lean_dec(x_59);
lean_inc_ref(x_55);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_60, 0, x_55);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_55);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_58);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_64, 0, x_57);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_65, 0, x_56);
lean_ctor_set(x_52, 4, x_63);
lean_ctor_set(x_52, 3, x_64);
lean_ctor_set(x_52, 2, x_65);
lean_ctor_set(x_52, 1, x_19);
lean_ctor_set(x_52, 0, x_62);
lean_ctor_set(x_11, 1, x_20);
x_66 = l_ReaderT_instMonad___redArg(x_11);
x_67 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_67, 0, lean_box(0));
lean_closure_set(x_67, 1, lean_box(0));
lean_closure_set(x_67, 2, x_66);
x_68 = l_instMonadControlTOfPure___redArg(x_67);
lean_inc_ref(x_68);
x_69 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_69, 0, x_50);
lean_closure_set(x_69, 1, x_68);
x_70 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_70, 0, x_50);
lean_closure_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_inc_ref(x_71);
x_72 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_72, 0, x_50);
lean_closure_set(x_72, 1, x_71);
x_73 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_73, 0, x_50);
lean_closure_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_inc_ref(x_74);
x_75 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_75, 0, x_50);
lean_closure_set(x_75, 1, x_74);
x_76 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_76, 0, x_50);
lean_closure_set(x_76, 1, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_inc_ref(x_77);
x_78 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_78, 0, x_50);
lean_closure_set(x_78, 1, x_77);
x_79 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_79, 0, x_50);
lean_closure_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_84, 0, x_1);
x_85 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_86 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_86, 0, lean_box(0));
lean_closure_set(x_86, 1, lean_box(0));
lean_closure_set(x_86, 2, x_48);
lean_closure_set(x_86, 3, lean_box(0));
lean_closure_set(x_86, 4, lean_box(0));
lean_closure_set(x_86, 5, x_85);
lean_closure_set(x_86, 6, x_84);
x_87 = l_Lean_MVarId_withContext___redArg(x_80, x_49, x_83, x_86);
lean_inc(x_2);
x_88 = lean_apply_9(x_87, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_st_ref_take(x_2);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
lean_ctor_set(x_93, 0, x_92);
x_96 = lean_st_ref_set(x_2, x_93);
lean_dec(x_2);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_93, 1);
x_98 = lean_ctor_get(x_93, 2);
x_99 = lean_ctor_get(x_93, 3);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_93);
x_100 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_97);
lean_ctor_set(x_100, 2, x_98);
lean_ctor_set(x_100, 3, x_99);
x_101 = lean_st_ref_set(x_2, x_100);
lean_dec(x_2);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_102 = lean_ctor_get(x_88, 0);
lean_inc(x_102);
lean_dec(x_88);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_st_ref_take(x_2);
x_106 = lean_ctor_get(x_105, 1);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_105, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 3);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 lean_ctor_release(x_105, 2);
 lean_ctor_release(x_105, 3);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 4, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_108);
x_111 = lean_st_ref_set(x_2, x_110);
lean_dec(x_2);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_103);
return x_112;
}
}
else
{
uint8_t x_113; 
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_88);
if (x_113 == 0)
{
return x_88;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_88, 0);
lean_inc(x_114);
lean_dec(x_88);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_116 = lean_ctor_get(x_52, 0);
x_117 = lean_ctor_get(x_52, 2);
x_118 = lean_ctor_get(x_52, 3);
x_119 = lean_ctor_get(x_52, 4);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_52);
lean_inc_ref(x_116);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_120, 0, x_116);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_121, 0, x_116);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_123, 0, x_119);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_124, 0, x_118);
x_125 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_125, 0, x_117);
x_126 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_19);
lean_ctor_set(x_126, 2, x_125);
lean_ctor_set(x_126, 3, x_124);
lean_ctor_set(x_126, 4, x_123);
lean_ctor_set(x_11, 1, x_20);
lean_ctor_set(x_11, 0, x_126);
x_127 = l_ReaderT_instMonad___redArg(x_11);
x_128 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_128, 0, lean_box(0));
lean_closure_set(x_128, 1, lean_box(0));
lean_closure_set(x_128, 2, x_127);
x_129 = l_instMonadControlTOfPure___redArg(x_128);
lean_inc_ref(x_129);
x_130 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_130, 0, x_50);
lean_closure_set(x_130, 1, x_129);
x_131 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_131, 0, x_50);
lean_closure_set(x_131, 1, x_129);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
lean_inc_ref(x_132);
x_133 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_133, 0, x_50);
lean_closure_set(x_133, 1, x_132);
x_134 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_134, 0, x_50);
lean_closure_set(x_134, 1, x_132);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
lean_inc_ref(x_135);
x_136 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_136, 0, x_50);
lean_closure_set(x_136, 1, x_135);
x_137 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_137, 0, x_50);
lean_closure_set(x_137, 1, x_135);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
lean_inc_ref(x_138);
x_139 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_139, 0, x_50);
lean_closure_set(x_139, 1, x_138);
x_140 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_140, 0, x_50);
lean_closure_set(x_140, 1, x_138);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_145, 0, x_1);
x_146 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_147 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_147, 0, lean_box(0));
lean_closure_set(x_147, 1, lean_box(0));
lean_closure_set(x_147, 2, x_48);
lean_closure_set(x_147, 3, lean_box(0));
lean_closure_set(x_147, 4, lean_box(0));
lean_closure_set(x_147, 5, x_146);
lean_closure_set(x_147, 6, x_145);
x_148 = l_Lean_MVarId_withContext___redArg(x_141, x_49, x_144, x_147);
lean_inc(x_2);
x_149 = lean_apply_9(x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_st_ref_take(x_2);
x_155 = lean_ctor_get(x_154, 1);
lean_inc_ref(x_155);
x_156 = lean_ctor_get(x_154, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 3);
lean_inc(x_157);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 x_158 = x_154;
} else {
 lean_dec_ref(x_154);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 4, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_153);
lean_ctor_set(x_159, 1, x_155);
lean_ctor_set(x_159, 2, x_156);
lean_ctor_set(x_159, 3, x_157);
x_160 = lean_st_ref_set(x_2, x_159);
lean_dec(x_2);
if (lean_is_scalar(x_151)) {
 x_161 = lean_alloc_ctor(0, 1, 0);
} else {
 x_161 = x_151;
}
lean_ctor_set(x_161, 0, x_152);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_162 = lean_ctor_get(x_149, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_163 = x_149;
} else {
 lean_dec_ref(x_149);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_165 = lean_ctor_get(x_11, 0);
lean_inc(x_165);
lean_dec(x_11);
x_166 = lean_ctor_get(x_165, 0);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_165, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_165, 4);
lean_inc(x_169);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 lean_ctor_release(x_165, 3);
 lean_ctor_release(x_165, 4);
 x_170 = x_165;
} else {
 lean_dec_ref(x_165);
 x_170 = lean_box(0);
}
lean_inc_ref(x_166);
x_171 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_171, 0, x_166);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_172, 0, x_166);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_174, 0, x_169);
x_175 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_175, 0, x_168);
x_176 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_176, 0, x_167);
if (lean_is_scalar(x_170)) {
 x_177 = lean_alloc_ctor(0, 5, 0);
} else {
 x_177 = x_170;
}
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_19);
lean_ctor_set(x_177, 2, x_176);
lean_ctor_set(x_177, 3, x_175);
lean_ctor_set(x_177, 4, x_174);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_20);
x_179 = l_ReaderT_instMonad___redArg(x_178);
x_180 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_180, 0, lean_box(0));
lean_closure_set(x_180, 1, lean_box(0));
lean_closure_set(x_180, 2, x_179);
x_181 = l_instMonadControlTOfPure___redArg(x_180);
lean_inc_ref(x_181);
x_182 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_182, 0, x_50);
lean_closure_set(x_182, 1, x_181);
x_183 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_183, 0, x_50);
lean_closure_set(x_183, 1, x_181);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
lean_inc_ref(x_184);
x_185 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_185, 0, x_50);
lean_closure_set(x_185, 1, x_184);
x_186 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_186, 0, x_50);
lean_closure_set(x_186, 1, x_184);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
lean_inc_ref(x_187);
x_188 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_188, 0, x_50);
lean_closure_set(x_188, 1, x_187);
x_189 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_189, 0, x_50);
lean_closure_set(x_189, 1, x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_inc_ref(x_190);
x_191 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_191, 0, x_50);
lean_closure_set(x_191, 1, x_190);
x_192 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_192, 0, x_50);
lean_closure_set(x_192, 1, x_190);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec_ref(x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
lean_dec(x_195);
x_197 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_197, 0, x_1);
x_198 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_199 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_199, 0, lean_box(0));
lean_closure_set(x_199, 1, lean_box(0));
lean_closure_set(x_199, 2, x_48);
lean_closure_set(x_199, 3, lean_box(0));
lean_closure_set(x_199, 4, lean_box(0));
lean_closure_set(x_199, 5, x_198);
lean_closure_set(x_199, 6, x_197);
x_200 = l_Lean_MVarId_withContext___redArg(x_193, x_49, x_196, x_199);
lean_inc(x_2);
x_201 = lean_apply_9(x_200, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_st_ref_take(x_2);
x_207 = lean_ctor_get(x_206, 1);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_206, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 3);
lean_inc(x_209);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 x_210 = x_206;
} else {
 lean_dec_ref(x_206);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 4, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_205);
lean_ctor_set(x_211, 1, x_207);
lean_ctor_set(x_211, 2, x_208);
lean_ctor_set(x_211, 3, x_209);
x_212 = lean_st_ref_set(x_2, x_211);
lean_dec(x_2);
if (lean_is_scalar(x_203)) {
 x_213 = lean_alloc_ctor(0, 1, 0);
} else {
 x_213 = x_203;
}
lean_ctor_set(x_213, 0, x_204);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_2);
x_214 = lean_ctor_get(x_201, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_215 = x_201;
} else {
 lean_dec_ref(x_201);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_214);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_217 = lean_ctor_get(x_30, 0);
x_218 = lean_ctor_get(x_30, 2);
x_219 = lean_ctor_get(x_30, 3);
x_220 = lean_ctor_get(x_30, 4);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_30);
x_221 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_222 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_217);
x_223 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_223, 0, x_217);
x_224 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_224, 0, x_217);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_226, 0, x_220);
x_227 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_227, 0, x_219);
x_228 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_228, 0, x_218);
x_229 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_229, 0, x_225);
lean_ctor_set(x_229, 1, x_221);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_227);
lean_ctor_set(x_229, 4, x_226);
lean_ctor_set(x_28, 1, x_222);
lean_ctor_set(x_28, 0, x_229);
x_230 = l_ReaderT_instMonad___redArg(x_28);
x_231 = l_ReaderT_instMonad___redArg(x_230);
x_232 = l_ReaderT_instMonad___redArg(x_231);
lean_inc_ref(x_232);
x_233 = l_ReaderT_instMonad___redArg(x_232);
x_234 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_235 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_235);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_236 = x_11;
} else {
 lean_dec_ref(x_11);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_235, 0);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_235, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_235, 4);
lean_inc(x_240);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 lean_ctor_release(x_235, 4);
 x_241 = x_235;
} else {
 lean_dec_ref(x_235);
 x_241 = lean_box(0);
}
lean_inc_ref(x_237);
x_242 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_242, 0, x_237);
x_243 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_243, 0, x_237);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_245, 0, x_240);
x_246 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_246, 0, x_239);
x_247 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_247, 0, x_238);
if (lean_is_scalar(x_241)) {
 x_248 = lean_alloc_ctor(0, 5, 0);
} else {
 x_248 = x_241;
}
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_19);
lean_ctor_set(x_248, 2, x_247);
lean_ctor_set(x_248, 3, x_246);
lean_ctor_set(x_248, 4, x_245);
if (lean_is_scalar(x_236)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_236;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_20);
x_250 = l_ReaderT_instMonad___redArg(x_249);
x_251 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_251, 0, lean_box(0));
lean_closure_set(x_251, 1, lean_box(0));
lean_closure_set(x_251, 2, x_250);
x_252 = l_instMonadControlTOfPure___redArg(x_251);
lean_inc_ref(x_252);
x_253 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_253, 0, x_234);
lean_closure_set(x_253, 1, x_252);
x_254 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_254, 0, x_234);
lean_closure_set(x_254, 1, x_252);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
lean_inc_ref(x_255);
x_256 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_256, 0, x_234);
lean_closure_set(x_256, 1, x_255);
x_257 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_257, 0, x_234);
lean_closure_set(x_257, 1, x_255);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
lean_inc_ref(x_258);
x_259 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_259, 0, x_234);
lean_closure_set(x_259, 1, x_258);
x_260 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_260, 0, x_234);
lean_closure_set(x_260, 1, x_258);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
lean_inc_ref(x_261);
x_262 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_262, 0, x_234);
lean_closure_set(x_262, 1, x_261);
x_263 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_263, 0, x_234);
lean_closure_set(x_263, 1, x_261);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec(x_266);
x_268 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_268, 0, x_1);
x_269 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_270 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_270, 0, lean_box(0));
lean_closure_set(x_270, 1, lean_box(0));
lean_closure_set(x_270, 2, x_232);
lean_closure_set(x_270, 3, lean_box(0));
lean_closure_set(x_270, 4, lean_box(0));
lean_closure_set(x_270, 5, x_269);
lean_closure_set(x_270, 6, x_268);
x_271 = l_Lean_MVarId_withContext___redArg(x_264, x_233, x_267, x_270);
lean_inc(x_2);
x_272 = lean_apply_9(x_271, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 x_274 = x_272;
} else {
 lean_dec_ref(x_272);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_273, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_276);
lean_dec(x_273);
x_277 = lean_st_ref_take(x_2);
x_278 = lean_ctor_get(x_277, 1);
lean_inc_ref(x_278);
x_279 = lean_ctor_get(x_277, 2);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 3);
lean_inc(x_280);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 lean_ctor_release(x_277, 2);
 lean_ctor_release(x_277, 3);
 x_281 = x_277;
} else {
 lean_dec_ref(x_277);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(0, 4, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_276);
lean_ctor_set(x_282, 1, x_278);
lean_ctor_set(x_282, 2, x_279);
lean_ctor_set(x_282, 3, x_280);
x_283 = lean_st_ref_set(x_2, x_282);
lean_dec(x_2);
if (lean_is_scalar(x_274)) {
 x_284 = lean_alloc_ctor(0, 1, 0);
} else {
 x_284 = x_274;
}
lean_ctor_set(x_284, 0, x_275);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_2);
x_285 = lean_ctor_get(x_272, 0);
lean_inc(x_285);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 x_286 = x_272;
} else {
 lean_dec_ref(x_272);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 1, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_285);
return x_287;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_288 = lean_ctor_get(x_28, 0);
lean_inc(x_288);
lean_dec(x_28);
x_289 = lean_ctor_get(x_288, 0);
lean_inc_ref(x_289);
x_290 = lean_ctor_get(x_288, 2);
lean_inc(x_290);
x_291 = lean_ctor_get(x_288, 3);
lean_inc(x_291);
x_292 = lean_ctor_get(x_288, 4);
lean_inc(x_292);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 lean_ctor_release(x_288, 4);
 x_293 = x_288;
} else {
 lean_dec_ref(x_288);
 x_293 = lean_box(0);
}
x_294 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_295 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_289);
x_296 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_296, 0, x_289);
x_297 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_297, 0, x_289);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_299, 0, x_292);
x_300 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_300, 0, x_291);
x_301 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_301, 0, x_290);
if (lean_is_scalar(x_293)) {
 x_302 = lean_alloc_ctor(0, 5, 0);
} else {
 x_302 = x_293;
}
lean_ctor_set(x_302, 0, x_298);
lean_ctor_set(x_302, 1, x_294);
lean_ctor_set(x_302, 2, x_301);
lean_ctor_set(x_302, 3, x_300);
lean_ctor_set(x_302, 4, x_299);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_295);
x_304 = l_ReaderT_instMonad___redArg(x_303);
x_305 = l_ReaderT_instMonad___redArg(x_304);
x_306 = l_ReaderT_instMonad___redArg(x_305);
lean_inc_ref(x_306);
x_307 = l_ReaderT_instMonad___redArg(x_306);
x_308 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_309 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_309);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_310 = x_11;
} else {
 lean_dec_ref(x_11);
 x_310 = lean_box(0);
}
x_311 = lean_ctor_get(x_309, 0);
lean_inc_ref(x_311);
x_312 = lean_ctor_get(x_309, 2);
lean_inc(x_312);
x_313 = lean_ctor_get(x_309, 3);
lean_inc(x_313);
x_314 = lean_ctor_get(x_309, 4);
lean_inc(x_314);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 lean_ctor_release(x_309, 2);
 lean_ctor_release(x_309, 3);
 lean_ctor_release(x_309, 4);
 x_315 = x_309;
} else {
 lean_dec_ref(x_309);
 x_315 = lean_box(0);
}
lean_inc_ref(x_311);
x_316 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_316, 0, x_311);
x_317 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_317, 0, x_311);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
x_319 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_319, 0, x_314);
x_320 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_320, 0, x_313);
x_321 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_321, 0, x_312);
if (lean_is_scalar(x_315)) {
 x_322 = lean_alloc_ctor(0, 5, 0);
} else {
 x_322 = x_315;
}
lean_ctor_set(x_322, 0, x_318);
lean_ctor_set(x_322, 1, x_19);
lean_ctor_set(x_322, 2, x_321);
lean_ctor_set(x_322, 3, x_320);
lean_ctor_set(x_322, 4, x_319);
if (lean_is_scalar(x_310)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_310;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_20);
x_324 = l_ReaderT_instMonad___redArg(x_323);
x_325 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_325, 0, lean_box(0));
lean_closure_set(x_325, 1, lean_box(0));
lean_closure_set(x_325, 2, x_324);
x_326 = l_instMonadControlTOfPure___redArg(x_325);
lean_inc_ref(x_326);
x_327 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_327, 0, x_308);
lean_closure_set(x_327, 1, x_326);
x_328 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_328, 0, x_308);
lean_closure_set(x_328, 1, x_326);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
lean_inc_ref(x_329);
x_330 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_330, 0, x_308);
lean_closure_set(x_330, 1, x_329);
x_331 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_331, 0, x_308);
lean_closure_set(x_331, 1, x_329);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
lean_inc_ref(x_332);
x_333 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_333, 0, x_308);
lean_closure_set(x_333, 1, x_332);
x_334 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_334, 0, x_308);
lean_closure_set(x_334, 1, x_332);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
lean_inc_ref(x_335);
x_336 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_336, 0, x_308);
lean_closure_set(x_336, 1, x_335);
x_337 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_337, 0, x_308);
lean_closure_set(x_337, 1, x_335);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec_ref(x_339);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
lean_dec(x_340);
x_342 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_342, 0, x_1);
x_343 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_344 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_344, 0, lean_box(0));
lean_closure_set(x_344, 1, lean_box(0));
lean_closure_set(x_344, 2, x_306);
lean_closure_set(x_344, 3, lean_box(0));
lean_closure_set(x_344, 4, lean_box(0));
lean_closure_set(x_344, 5, x_343);
lean_closure_set(x_344, 6, x_342);
x_345 = l_Lean_MVarId_withContext___redArg(x_338, x_307, x_341, x_344);
lean_inc(x_2);
x_346 = lean_apply_9(x_345, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_348 = x_346;
} else {
 lean_dec_ref(x_346);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
x_351 = lean_st_ref_take(x_2);
x_352 = lean_ctor_get(x_351, 1);
lean_inc_ref(x_352);
x_353 = lean_ctor_get(x_351, 2);
lean_inc(x_353);
x_354 = lean_ctor_get(x_351, 3);
lean_inc(x_354);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_355 = x_351;
} else {
 lean_dec_ref(x_351);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(0, 4, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_350);
lean_ctor_set(x_356, 1, x_352);
lean_ctor_set(x_356, 2, x_353);
lean_ctor_set(x_356, 3, x_354);
x_357 = lean_st_ref_set(x_2, x_356);
lean_dec(x_2);
if (lean_is_scalar(x_348)) {
 x_358 = lean_alloc_ctor(0, 1, 0);
} else {
 x_358 = x_348;
}
lean_ctor_set(x_358, 0, x_349);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_2);
x_359 = lean_ctor_get(x_346, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 x_360 = x_346;
} else {
 lean_dec_ref(x_346);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_359);
return x_361;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_362 = lean_ctor_get(x_12, 0);
x_363 = lean_ctor_get(x_12, 2);
x_364 = lean_ctor_get(x_12, 3);
x_365 = lean_ctor_get(x_12, 4);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_12);
x_366 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_367 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_362);
x_368 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_368, 0, x_362);
x_369 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_369, 0, x_362);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
x_371 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_371, 0, x_365);
x_372 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_372, 0, x_364);
x_373 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_373, 0, x_363);
x_374 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_374, 0, x_370);
lean_ctor_set(x_374, 1, x_366);
lean_ctor_set(x_374, 2, x_373);
lean_ctor_set(x_374, 3, x_372);
lean_ctor_set(x_374, 4, x_371);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_367);
x_376 = l_ReaderT_instMonad___redArg(x_375);
x_377 = lean_ctor_get(x_376, 0);
lean_inc_ref(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_377, 0);
lean_inc_ref(x_379);
x_380 = lean_ctor_get(x_377, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_377, 3);
lean_inc(x_381);
x_382 = lean_ctor_get(x_377, 4);
lean_inc(x_382);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 lean_ctor_release(x_377, 4);
 x_383 = x_377;
} else {
 lean_dec_ref(x_377);
 x_383 = lean_box(0);
}
x_384 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_385 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_379);
x_386 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_386, 0, x_379);
x_387 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_387, 0, x_379);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
x_389 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_389, 0, x_382);
x_390 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_390, 0, x_381);
x_391 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_391, 0, x_380);
if (lean_is_scalar(x_383)) {
 x_392 = lean_alloc_ctor(0, 5, 0);
} else {
 x_392 = x_383;
}
lean_ctor_set(x_392, 0, x_388);
lean_ctor_set(x_392, 1, x_384);
lean_ctor_set(x_392, 2, x_391);
lean_ctor_set(x_392, 3, x_390);
lean_ctor_set(x_392, 4, x_389);
if (lean_is_scalar(x_378)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_378;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_385);
x_394 = l_ReaderT_instMonad___redArg(x_393);
x_395 = l_ReaderT_instMonad___redArg(x_394);
x_396 = l_ReaderT_instMonad___redArg(x_395);
lean_inc_ref(x_396);
x_397 = l_ReaderT_instMonad___redArg(x_396);
x_398 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_399 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_399);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_400 = x_11;
} else {
 lean_dec_ref(x_11);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_399, 0);
lean_inc_ref(x_401);
x_402 = lean_ctor_get(x_399, 2);
lean_inc(x_402);
x_403 = lean_ctor_get(x_399, 3);
lean_inc(x_403);
x_404 = lean_ctor_get(x_399, 4);
lean_inc(x_404);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 lean_ctor_release(x_399, 2);
 lean_ctor_release(x_399, 3);
 lean_ctor_release(x_399, 4);
 x_405 = x_399;
} else {
 lean_dec_ref(x_399);
 x_405 = lean_box(0);
}
lean_inc_ref(x_401);
x_406 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_406, 0, x_401);
x_407 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_407, 0, x_401);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
x_409 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_409, 0, x_404);
x_410 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_410, 0, x_403);
x_411 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_411, 0, x_402);
if (lean_is_scalar(x_405)) {
 x_412 = lean_alloc_ctor(0, 5, 0);
} else {
 x_412 = x_405;
}
lean_ctor_set(x_412, 0, x_408);
lean_ctor_set(x_412, 1, x_366);
lean_ctor_set(x_412, 2, x_411);
lean_ctor_set(x_412, 3, x_410);
lean_ctor_set(x_412, 4, x_409);
if (lean_is_scalar(x_400)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_400;
}
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_367);
x_414 = l_ReaderT_instMonad___redArg(x_413);
x_415 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_415, 0, lean_box(0));
lean_closure_set(x_415, 1, lean_box(0));
lean_closure_set(x_415, 2, x_414);
x_416 = l_instMonadControlTOfPure___redArg(x_415);
lean_inc_ref(x_416);
x_417 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_417, 0, x_398);
lean_closure_set(x_417, 1, x_416);
x_418 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_418, 0, x_398);
lean_closure_set(x_418, 1, x_416);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_418);
lean_inc_ref(x_419);
x_420 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_420, 0, x_398);
lean_closure_set(x_420, 1, x_419);
x_421 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_421, 0, x_398);
lean_closure_set(x_421, 1, x_419);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
lean_inc_ref(x_422);
x_423 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_423, 0, x_398);
lean_closure_set(x_423, 1, x_422);
x_424 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_424, 0, x_398);
lean_closure_set(x_424, 1, x_422);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
lean_inc_ref(x_425);
x_426 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_426, 0, x_398);
lean_closure_set(x_426, 1, x_425);
x_427 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_427, 0, x_398);
lean_closure_set(x_427, 1, x_425);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
x_429 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
lean_dec_ref(x_429);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
lean_dec(x_430);
x_432 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_432, 0, x_1);
x_433 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_434 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_434, 0, lean_box(0));
lean_closure_set(x_434, 1, lean_box(0));
lean_closure_set(x_434, 2, x_396);
lean_closure_set(x_434, 3, lean_box(0));
lean_closure_set(x_434, 4, lean_box(0));
lean_closure_set(x_434, 5, x_433);
lean_closure_set(x_434, 6, x_432);
x_435 = l_Lean_MVarId_withContext___redArg(x_428, x_397, x_431, x_434);
lean_inc(x_2);
x_436 = lean_apply_9(x_435, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_438 = x_436;
} else {
 lean_dec_ref(x_436);
 x_438 = lean_box(0);
}
x_439 = lean_ctor_get(x_437, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_437, 1);
lean_inc(x_440);
lean_dec(x_437);
x_441 = lean_st_ref_take(x_2);
x_442 = lean_ctor_get(x_441, 1);
lean_inc_ref(x_442);
x_443 = lean_ctor_get(x_441, 2);
lean_inc(x_443);
x_444 = lean_ctor_get(x_441, 3);
lean_inc(x_444);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 lean_ctor_release(x_441, 2);
 lean_ctor_release(x_441, 3);
 x_445 = x_441;
} else {
 lean_dec_ref(x_441);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(0, 4, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_440);
lean_ctor_set(x_446, 1, x_442);
lean_ctor_set(x_446, 2, x_443);
lean_ctor_set(x_446, 3, x_444);
x_447 = lean_st_ref_set(x_2, x_446);
lean_dec(x_2);
if (lean_is_scalar(x_438)) {
 x_448 = lean_alloc_ctor(0, 1, 0);
} else {
 x_448 = x_438;
}
lean_ctor_set(x_448, 0, x_439);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_2);
x_449 = lean_ctor_get(x_436, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_450 = x_436;
} else {
 lean_dec_ref(x_436);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 1, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_449);
return x_451;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1;
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 2);
x_17 = lean_ctor_get(x_13, 3);
x_18 = lean_ctor_get(x_13, 4);
x_19 = lean_ctor_get(x_13, 1);
lean_dec(x_19);
x_20 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_21 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_16);
lean_ctor_set(x_13, 4, x_25);
lean_ctor_set(x_13, 3, x_26);
lean_ctor_set(x_13, 2, x_27);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_21);
x_29 = l_ReaderT_instMonad___redArg(x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_38 = lean_ctor_get(x_31, 1);
lean_dec(x_38);
x_39 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_40 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_36);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_35);
lean_ctor_set(x_31, 4, x_44);
lean_ctor_set(x_31, 3, x_45);
lean_ctor_set(x_31, 2, x_46);
lean_ctor_set(x_31, 1, x_39);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_29, 1, x_40);
x_47 = l_ReaderT_instMonad___redArg(x_29);
x_48 = l_ReaderT_instMonad___redArg(x_47);
x_49 = l_ReaderT_instMonad___redArg(x_48);
lean_inc_ref(x_49);
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_52 = !lean_is_exclusive(x_12);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_12, 0);
x_54 = lean_ctor_get(x_12, 1);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_ctor_get(x_53, 2);
x_58 = lean_ctor_get(x_53, 3);
x_59 = lean_ctor_get(x_53, 4);
x_60 = lean_ctor_get(x_53, 1);
lean_dec(x_60);
lean_inc_ref(x_56);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_61, 0, x_56);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_62, 0, x_56);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_64, 0, x_59);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_65, 0, x_58);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_66, 0, x_57);
lean_ctor_set(x_53, 4, x_64);
lean_ctor_set(x_53, 3, x_65);
lean_ctor_set(x_53, 2, x_66);
lean_ctor_set(x_53, 1, x_20);
lean_ctor_set(x_53, 0, x_63);
lean_ctor_set(x_12, 1, x_21);
x_67 = l_ReaderT_instMonad___redArg(x_12);
x_68 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_68, 0, lean_box(0));
lean_closure_set(x_68, 1, lean_box(0));
lean_closure_set(x_68, 2, x_67);
x_69 = l_instMonadControlTOfPure___redArg(x_68);
lean_inc_ref(x_69);
x_70 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_70, 0, x_51);
lean_closure_set(x_70, 1, x_69);
x_71 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_71, 0, x_51);
lean_closure_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_inc_ref(x_72);
x_73 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_73, 0, x_51);
lean_closure_set(x_73, 1, x_72);
x_74 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_74, 0, x_51);
lean_closure_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc_ref(x_75);
x_76 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_76, 0, x_51);
lean_closure_set(x_76, 1, x_75);
x_77 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_77, 0, x_51);
lean_closure_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
lean_inc_ref(x_78);
x_79 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_79, 0, x_51);
lean_closure_set(x_79, 1, x_78);
x_80 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_80, 0, x_51);
lean_closure_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_85, 0, x_2);
x_86 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_87 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_87, 0, lean_box(0));
lean_closure_set(x_87, 1, lean_box(0));
lean_closure_set(x_87, 2, x_49);
lean_closure_set(x_87, 3, lean_box(0));
lean_closure_set(x_87, 4, lean_box(0));
lean_closure_set(x_87, 5, x_86);
lean_closure_set(x_87, 6, x_85);
x_88 = l_Lean_MVarId_withContext___redArg(x_81, x_50, x_84, x_87);
lean_inc(x_3);
x_89 = lean_apply_9(x_88, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_st_ref_take(x_3);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set(x_94, 0, x_93);
x_97 = lean_st_ref_set(x_3, x_94);
lean_dec(x_3);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_94, 1);
x_99 = lean_ctor_get(x_94, 2);
x_100 = lean_ctor_get(x_94, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_94);
x_101 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_101, 0, x_93);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_100);
x_102 = lean_st_ref_set(x_3, x_101);
lean_dec(x_3);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_89, 0);
lean_inc(x_103);
lean_dec(x_89);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_st_ref_take(x_3);
x_107 = lean_ctor_get(x_106, 1);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_106, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 3);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 4, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_107);
lean_ctor_set(x_111, 2, x_108);
lean_ctor_set(x_111, 3, x_109);
x_112 = lean_st_ref_set(x_3, x_111);
lean_dec(x_3);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_104);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_89);
if (x_114 == 0)
{
return x_89;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_89, 0);
lean_inc(x_115);
lean_dec(x_89);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_117 = lean_ctor_get(x_53, 0);
x_118 = lean_ctor_get(x_53, 2);
x_119 = lean_ctor_get(x_53, 3);
x_120 = lean_ctor_get(x_53, 4);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_53);
lean_inc_ref(x_117);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_121, 0, x_117);
x_122 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_122, 0, x_117);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_124, 0, x_120);
x_125 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_125, 0, x_119);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_126, 0, x_118);
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_20);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_125);
lean_ctor_set(x_127, 4, x_124);
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_127);
x_128 = l_ReaderT_instMonad___redArg(x_12);
x_129 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_129, 0, lean_box(0));
lean_closure_set(x_129, 1, lean_box(0));
lean_closure_set(x_129, 2, x_128);
x_130 = l_instMonadControlTOfPure___redArg(x_129);
lean_inc_ref(x_130);
x_131 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_131, 0, x_51);
lean_closure_set(x_131, 1, x_130);
x_132 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_132, 0, x_51);
lean_closure_set(x_132, 1, x_130);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
lean_inc_ref(x_133);
x_134 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_134, 0, x_51);
lean_closure_set(x_134, 1, x_133);
x_135 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_135, 0, x_51);
lean_closure_set(x_135, 1, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_inc_ref(x_136);
x_137 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_137, 0, x_51);
lean_closure_set(x_137, 1, x_136);
x_138 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_138, 0, x_51);
lean_closure_set(x_138, 1, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_inc_ref(x_139);
x_140 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_140, 0, x_51);
lean_closure_set(x_140, 1, x_139);
x_141 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_141, 0, x_51);
lean_closure_set(x_141, 1, x_139);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_146, 0, x_2);
x_147 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_148 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_148, 0, lean_box(0));
lean_closure_set(x_148, 1, lean_box(0));
lean_closure_set(x_148, 2, x_49);
lean_closure_set(x_148, 3, lean_box(0));
lean_closure_set(x_148, 4, lean_box(0));
lean_closure_set(x_148, 5, x_147);
lean_closure_set(x_148, 6, x_146);
x_149 = l_Lean_MVarId_withContext___redArg(x_142, x_50, x_145, x_148);
lean_inc(x_3);
x_150 = lean_apply_9(x_149, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_st_ref_take(x_3);
x_156 = lean_ctor_get(x_155, 1);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_155, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 3);
lean_inc(x_158);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 x_159 = x_155;
} else {
 lean_dec_ref(x_155);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 4, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_156);
lean_ctor_set(x_160, 2, x_157);
lean_ctor_set(x_160, 3, x_158);
x_161 = lean_st_ref_set(x_3, x_160);
lean_dec(x_3);
if (lean_is_scalar(x_152)) {
 x_162 = lean_alloc_ctor(0, 1, 0);
} else {
 x_162 = x_152;
}
lean_ctor_set(x_162, 0, x_153);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_3);
x_163 = lean_ctor_get(x_150, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_164 = x_150;
} else {
 lean_dec_ref(x_150);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_166 = lean_ctor_get(x_12, 0);
lean_inc(x_166);
lean_dec(x_12);
x_167 = lean_ctor_get(x_166, 0);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_166, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_166, 4);
lean_inc(x_170);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 x_171 = x_166;
} else {
 lean_dec_ref(x_166);
 x_171 = lean_box(0);
}
lean_inc_ref(x_167);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_172, 0, x_167);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_173, 0, x_167);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_175, 0, x_170);
x_176 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_176, 0, x_169);
x_177 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_177, 0, x_168);
if (lean_is_scalar(x_171)) {
 x_178 = lean_alloc_ctor(0, 5, 0);
} else {
 x_178 = x_171;
}
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_20);
lean_ctor_set(x_178, 2, x_177);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set(x_178, 4, x_175);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_21);
x_180 = l_ReaderT_instMonad___redArg(x_179);
x_181 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_181, 0, lean_box(0));
lean_closure_set(x_181, 1, lean_box(0));
lean_closure_set(x_181, 2, x_180);
x_182 = l_instMonadControlTOfPure___redArg(x_181);
lean_inc_ref(x_182);
x_183 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_183, 0, x_51);
lean_closure_set(x_183, 1, x_182);
x_184 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_184, 0, x_51);
lean_closure_set(x_184, 1, x_182);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
lean_inc_ref(x_185);
x_186 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_186, 0, x_51);
lean_closure_set(x_186, 1, x_185);
x_187 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_187, 0, x_51);
lean_closure_set(x_187, 1, x_185);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
lean_inc_ref(x_188);
x_189 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_189, 0, x_51);
lean_closure_set(x_189, 1, x_188);
x_190 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_190, 0, x_51);
lean_closure_set(x_190, 1, x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
lean_inc_ref(x_191);
x_192 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_192, 0, x_51);
lean_closure_set(x_192, 1, x_191);
x_193 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_193, 0, x_51);
lean_closure_set(x_193, 1, x_191);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
lean_dec_ref(x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec(x_196);
x_198 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_198, 0, x_2);
x_199 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_200 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_200, 0, lean_box(0));
lean_closure_set(x_200, 1, lean_box(0));
lean_closure_set(x_200, 2, x_49);
lean_closure_set(x_200, 3, lean_box(0));
lean_closure_set(x_200, 4, lean_box(0));
lean_closure_set(x_200, 5, x_199);
lean_closure_set(x_200, 6, x_198);
x_201 = l_Lean_MVarId_withContext___redArg(x_194, x_50, x_197, x_200);
lean_inc(x_3);
x_202 = lean_apply_9(x_201, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_dec(x_203);
x_207 = lean_st_ref_take(x_3);
x_208 = lean_ctor_get(x_207, 1);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_207, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_207, 3);
lean_inc(x_210);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_211 = x_207;
} else {
 lean_dec_ref(x_207);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 4, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_206);
lean_ctor_set(x_212, 1, x_208);
lean_ctor_set(x_212, 2, x_209);
lean_ctor_set(x_212, 3, x_210);
x_213 = lean_st_ref_set(x_3, x_212);
lean_dec(x_3);
if (lean_is_scalar(x_204)) {
 x_214 = lean_alloc_ctor(0, 1, 0);
} else {
 x_214 = x_204;
}
lean_ctor_set(x_214, 0, x_205);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_3);
x_215 = lean_ctor_get(x_202, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_216 = x_202;
} else {
 lean_dec_ref(x_202);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_218 = lean_ctor_get(x_31, 0);
x_219 = lean_ctor_get(x_31, 2);
x_220 = lean_ctor_get(x_31, 3);
x_221 = lean_ctor_get(x_31, 4);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_31);
x_222 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_223 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_218);
x_224 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_224, 0, x_218);
x_225 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_225, 0, x_218);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_227, 0, x_221);
x_228 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_228, 0, x_220);
x_229 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_229, 0, x_219);
x_230 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_222);
lean_ctor_set(x_230, 2, x_229);
lean_ctor_set(x_230, 3, x_228);
lean_ctor_set(x_230, 4, x_227);
lean_ctor_set(x_29, 1, x_223);
lean_ctor_set(x_29, 0, x_230);
x_231 = l_ReaderT_instMonad___redArg(x_29);
x_232 = l_ReaderT_instMonad___redArg(x_231);
x_233 = l_ReaderT_instMonad___redArg(x_232);
lean_inc_ref(x_233);
x_234 = l_ReaderT_instMonad___redArg(x_233);
x_235 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_236 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_236);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_237 = x_12;
} else {
 lean_dec_ref(x_12);
 x_237 = lean_box(0);
}
x_238 = lean_ctor_get(x_236, 0);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_236, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 3);
lean_inc(x_240);
x_241 = lean_ctor_get(x_236, 4);
lean_inc(x_241);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 lean_ctor_release(x_236, 4);
 x_242 = x_236;
} else {
 lean_dec_ref(x_236);
 x_242 = lean_box(0);
}
lean_inc_ref(x_238);
x_243 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_243, 0, x_238);
x_244 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_244, 0, x_238);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_246, 0, x_241);
x_247 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_247, 0, x_240);
x_248 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_248, 0, x_239);
if (lean_is_scalar(x_242)) {
 x_249 = lean_alloc_ctor(0, 5, 0);
} else {
 x_249 = x_242;
}
lean_ctor_set(x_249, 0, x_245);
lean_ctor_set(x_249, 1, x_20);
lean_ctor_set(x_249, 2, x_248);
lean_ctor_set(x_249, 3, x_247);
lean_ctor_set(x_249, 4, x_246);
if (lean_is_scalar(x_237)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_237;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_21);
x_251 = l_ReaderT_instMonad___redArg(x_250);
x_252 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_252, 0, lean_box(0));
lean_closure_set(x_252, 1, lean_box(0));
lean_closure_set(x_252, 2, x_251);
x_253 = l_instMonadControlTOfPure___redArg(x_252);
lean_inc_ref(x_253);
x_254 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_254, 0, x_235);
lean_closure_set(x_254, 1, x_253);
x_255 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_255, 0, x_235);
lean_closure_set(x_255, 1, x_253);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
lean_inc_ref(x_256);
x_257 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_257, 0, x_235);
lean_closure_set(x_257, 1, x_256);
x_258 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_258, 0, x_235);
lean_closure_set(x_258, 1, x_256);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
lean_inc_ref(x_259);
x_260 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_260, 0, x_235);
lean_closure_set(x_260, 1, x_259);
x_261 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_261, 0, x_235);
lean_closure_set(x_261, 1, x_259);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
lean_inc_ref(x_262);
x_263 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_263, 0, x_235);
lean_closure_set(x_263, 1, x_262);
x_264 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_264, 0, x_235);
lean_closure_set(x_264, 1, x_262);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec_ref(x_266);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec(x_267);
x_269 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_269, 0, x_2);
x_270 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_271 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_271, 0, lean_box(0));
lean_closure_set(x_271, 1, lean_box(0));
lean_closure_set(x_271, 2, x_233);
lean_closure_set(x_271, 3, lean_box(0));
lean_closure_set(x_271, 4, lean_box(0));
lean_closure_set(x_271, 5, x_270);
lean_closure_set(x_271, 6, x_269);
x_272 = l_Lean_MVarId_withContext___redArg(x_265, x_234, x_268, x_271);
lean_inc(x_3);
x_273 = lean_apply_9(x_272, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_275 = x_273;
} else {
 lean_dec_ref(x_273);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_274, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
lean_dec(x_274);
x_278 = lean_st_ref_take(x_3);
x_279 = lean_ctor_get(x_278, 1);
lean_inc_ref(x_279);
x_280 = lean_ctor_get(x_278, 2);
lean_inc(x_280);
x_281 = lean_ctor_get(x_278, 3);
lean_inc(x_281);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 lean_ctor_release(x_278, 3);
 x_282 = x_278;
} else {
 lean_dec_ref(x_278);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 4, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_279);
lean_ctor_set(x_283, 2, x_280);
lean_ctor_set(x_283, 3, x_281);
x_284 = lean_st_ref_set(x_3, x_283);
lean_dec(x_3);
if (lean_is_scalar(x_275)) {
 x_285 = lean_alloc_ctor(0, 1, 0);
} else {
 x_285 = x_275;
}
lean_ctor_set(x_285, 0, x_276);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_3);
x_286 = lean_ctor_get(x_273, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_287 = x_273;
} else {
 lean_dec_ref(x_273);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 1, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_286);
return x_288;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_289 = lean_ctor_get(x_29, 0);
lean_inc(x_289);
lean_dec(x_29);
x_290 = lean_ctor_get(x_289, 0);
lean_inc_ref(x_290);
x_291 = lean_ctor_get(x_289, 2);
lean_inc(x_291);
x_292 = lean_ctor_get(x_289, 3);
lean_inc(x_292);
x_293 = lean_ctor_get(x_289, 4);
lean_inc(x_293);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 lean_ctor_release(x_289, 2);
 lean_ctor_release(x_289, 3);
 lean_ctor_release(x_289, 4);
 x_294 = x_289;
} else {
 lean_dec_ref(x_289);
 x_294 = lean_box(0);
}
x_295 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_296 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_290);
x_297 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_297, 0, x_290);
x_298 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_298, 0, x_290);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_300, 0, x_293);
x_301 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_301, 0, x_292);
x_302 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_302, 0, x_291);
if (lean_is_scalar(x_294)) {
 x_303 = lean_alloc_ctor(0, 5, 0);
} else {
 x_303 = x_294;
}
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_295);
lean_ctor_set(x_303, 2, x_302);
lean_ctor_set(x_303, 3, x_301);
lean_ctor_set(x_303, 4, x_300);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_296);
x_305 = l_ReaderT_instMonad___redArg(x_304);
x_306 = l_ReaderT_instMonad___redArg(x_305);
x_307 = l_ReaderT_instMonad___redArg(x_306);
lean_inc_ref(x_307);
x_308 = l_ReaderT_instMonad___redArg(x_307);
x_309 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_310 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_310);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_311 = x_12;
} else {
 lean_dec_ref(x_12);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_310, 0);
lean_inc_ref(x_312);
x_313 = lean_ctor_get(x_310, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_310, 3);
lean_inc(x_314);
x_315 = lean_ctor_get(x_310, 4);
lean_inc(x_315);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 lean_ctor_release(x_310, 2);
 lean_ctor_release(x_310, 3);
 lean_ctor_release(x_310, 4);
 x_316 = x_310;
} else {
 lean_dec_ref(x_310);
 x_316 = lean_box(0);
}
lean_inc_ref(x_312);
x_317 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_317, 0, x_312);
x_318 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_318, 0, x_312);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
x_320 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_320, 0, x_315);
x_321 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_321, 0, x_314);
x_322 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_322, 0, x_313);
if (lean_is_scalar(x_316)) {
 x_323 = lean_alloc_ctor(0, 5, 0);
} else {
 x_323 = x_316;
}
lean_ctor_set(x_323, 0, x_319);
lean_ctor_set(x_323, 1, x_20);
lean_ctor_set(x_323, 2, x_322);
lean_ctor_set(x_323, 3, x_321);
lean_ctor_set(x_323, 4, x_320);
if (lean_is_scalar(x_311)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_311;
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_21);
x_325 = l_ReaderT_instMonad___redArg(x_324);
x_326 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_326, 0, lean_box(0));
lean_closure_set(x_326, 1, lean_box(0));
lean_closure_set(x_326, 2, x_325);
x_327 = l_instMonadControlTOfPure___redArg(x_326);
lean_inc_ref(x_327);
x_328 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_328, 0, x_309);
lean_closure_set(x_328, 1, x_327);
x_329 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_329, 0, x_309);
lean_closure_set(x_329, 1, x_327);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
lean_inc_ref(x_330);
x_331 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_331, 0, x_309);
lean_closure_set(x_331, 1, x_330);
x_332 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_332, 0, x_309);
lean_closure_set(x_332, 1, x_330);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
lean_inc_ref(x_333);
x_334 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_334, 0, x_309);
lean_closure_set(x_334, 1, x_333);
x_335 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_335, 0, x_309);
lean_closure_set(x_335, 1, x_333);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
lean_inc_ref(x_336);
x_337 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_337, 0, x_309);
lean_closure_set(x_337, 1, x_336);
x_338 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_338, 0, x_309);
lean_closure_set(x_338, 1, x_336);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_340 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
lean_dec_ref(x_340);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
lean_dec(x_341);
x_343 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_343, 0, x_2);
x_344 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_345 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_345, 0, lean_box(0));
lean_closure_set(x_345, 1, lean_box(0));
lean_closure_set(x_345, 2, x_307);
lean_closure_set(x_345, 3, lean_box(0));
lean_closure_set(x_345, 4, lean_box(0));
lean_closure_set(x_345, 5, x_344);
lean_closure_set(x_345, 6, x_343);
x_346 = l_Lean_MVarId_withContext___redArg(x_339, x_308, x_342, x_345);
lean_inc(x_3);
x_347 = lean_apply_9(x_346, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 x_349 = x_347;
} else {
 lean_dec_ref(x_347);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_348, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_351);
lean_dec(x_348);
x_352 = lean_st_ref_take(x_3);
x_353 = lean_ctor_get(x_352, 1);
lean_inc_ref(x_353);
x_354 = lean_ctor_get(x_352, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_352, 3);
lean_inc(x_355);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 lean_ctor_release(x_352, 3);
 x_356 = x_352;
} else {
 lean_dec_ref(x_352);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(0, 4, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_351);
lean_ctor_set(x_357, 1, x_353);
lean_ctor_set(x_357, 2, x_354);
lean_ctor_set(x_357, 3, x_355);
x_358 = lean_st_ref_set(x_3, x_357);
lean_dec(x_3);
if (lean_is_scalar(x_349)) {
 x_359 = lean_alloc_ctor(0, 1, 0);
} else {
 x_359 = x_349;
}
lean_ctor_set(x_359, 0, x_350);
return x_359;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_3);
x_360 = lean_ctor_get(x_347, 0);
lean_inc(x_360);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 x_361 = x_347;
} else {
 lean_dec_ref(x_347);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 1, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_360);
return x_362;
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_363 = lean_ctor_get(x_13, 0);
x_364 = lean_ctor_get(x_13, 2);
x_365 = lean_ctor_get(x_13, 3);
x_366 = lean_ctor_get(x_13, 4);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_13);
x_367 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_368 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_363);
x_369 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_369, 0, x_363);
x_370 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_370, 0, x_363);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_372 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_372, 0, x_366);
x_373 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_373, 0, x_365);
x_374 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_374, 0, x_364);
x_375 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_375, 0, x_371);
lean_ctor_set(x_375, 1, x_367);
lean_ctor_set(x_375, 2, x_374);
lean_ctor_set(x_375, 3, x_373);
lean_ctor_set(x_375, 4, x_372);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_368);
x_377 = l_ReaderT_instMonad___redArg(x_376);
x_378 = lean_ctor_get(x_377, 0);
lean_inc_ref(x_378);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_379 = x_377;
} else {
 lean_dec_ref(x_377);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_378, 0);
lean_inc_ref(x_380);
x_381 = lean_ctor_get(x_378, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_378, 3);
lean_inc(x_382);
x_383 = lean_ctor_get(x_378, 4);
lean_inc(x_383);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 lean_ctor_release(x_378, 4);
 x_384 = x_378;
} else {
 lean_dec_ref(x_378);
 x_384 = lean_box(0);
}
x_385 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_386 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_380);
x_387 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_387, 0, x_380);
x_388 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_388, 0, x_380);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_390, 0, x_383);
x_391 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_391, 0, x_382);
x_392 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_392, 0, x_381);
if (lean_is_scalar(x_384)) {
 x_393 = lean_alloc_ctor(0, 5, 0);
} else {
 x_393 = x_384;
}
lean_ctor_set(x_393, 0, x_389);
lean_ctor_set(x_393, 1, x_385);
lean_ctor_set(x_393, 2, x_392);
lean_ctor_set(x_393, 3, x_391);
lean_ctor_set(x_393, 4, x_390);
if (lean_is_scalar(x_379)) {
 x_394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_394 = x_379;
}
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_386);
x_395 = l_ReaderT_instMonad___redArg(x_394);
x_396 = l_ReaderT_instMonad___redArg(x_395);
x_397 = l_ReaderT_instMonad___redArg(x_396);
lean_inc_ref(x_397);
x_398 = l_ReaderT_instMonad___redArg(x_397);
x_399 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_400 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_400);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_401 = x_12;
} else {
 lean_dec_ref(x_12);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_400, 0);
lean_inc_ref(x_402);
x_403 = lean_ctor_get(x_400, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_400, 3);
lean_inc(x_404);
x_405 = lean_ctor_get(x_400, 4);
lean_inc(x_405);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 lean_ctor_release(x_400, 2);
 lean_ctor_release(x_400, 3);
 lean_ctor_release(x_400, 4);
 x_406 = x_400;
} else {
 lean_dec_ref(x_400);
 x_406 = lean_box(0);
}
lean_inc_ref(x_402);
x_407 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_407, 0, x_402);
x_408 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_408, 0, x_402);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_410, 0, x_405);
x_411 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_411, 0, x_404);
x_412 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_412, 0, x_403);
if (lean_is_scalar(x_406)) {
 x_413 = lean_alloc_ctor(0, 5, 0);
} else {
 x_413 = x_406;
}
lean_ctor_set(x_413, 0, x_409);
lean_ctor_set(x_413, 1, x_367);
lean_ctor_set(x_413, 2, x_412);
lean_ctor_set(x_413, 3, x_411);
lean_ctor_set(x_413, 4, x_410);
if (lean_is_scalar(x_401)) {
 x_414 = lean_alloc_ctor(0, 2, 0);
} else {
 x_414 = x_401;
}
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_368);
x_415 = l_ReaderT_instMonad___redArg(x_414);
x_416 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_416, 0, lean_box(0));
lean_closure_set(x_416, 1, lean_box(0));
lean_closure_set(x_416, 2, x_415);
x_417 = l_instMonadControlTOfPure___redArg(x_416);
lean_inc_ref(x_417);
x_418 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_418, 0, x_399);
lean_closure_set(x_418, 1, x_417);
x_419 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_419, 0, x_399);
lean_closure_set(x_419, 1, x_417);
x_420 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
lean_inc_ref(x_420);
x_421 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_421, 0, x_399);
lean_closure_set(x_421, 1, x_420);
x_422 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_422, 0, x_399);
lean_closure_set(x_422, 1, x_420);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
lean_inc_ref(x_423);
x_424 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_424, 0, x_399);
lean_closure_set(x_424, 1, x_423);
x_425 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_425, 0, x_399);
lean_closure_set(x_425, 1, x_423);
x_426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
lean_inc_ref(x_426);
x_427 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_427, 0, x_399);
lean_closure_set(x_427, 1, x_426);
x_428 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_428, 0, x_399);
lean_closure_set(x_428, 1, x_426);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
x_430 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
lean_dec_ref(x_430);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
lean_dec(x_431);
x_433 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed), 11, 1);
lean_closure_set(x_433, 0, x_2);
x_434 = l_Lean_Meta_Grind_liftGoalM___redArg___closed__14;
x_435 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_435, 0, lean_box(0));
lean_closure_set(x_435, 1, lean_box(0));
lean_closure_set(x_435, 2, x_397);
lean_closure_set(x_435, 3, lean_box(0));
lean_closure_set(x_435, 4, lean_box(0));
lean_closure_set(x_435, 5, x_434);
lean_closure_set(x_435, 6, x_433);
x_436 = l_Lean_MVarId_withContext___redArg(x_429, x_398, x_432, x_435);
lean_inc(x_3);
x_437 = lean_apply_9(x_436, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 x_439 = x_437;
} else {
 lean_dec_ref(x_437);
 x_439 = lean_box(0);
}
x_440 = lean_ctor_get(x_438, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_441);
lean_dec(x_438);
x_442 = lean_st_ref_take(x_3);
x_443 = lean_ctor_get(x_442, 1);
lean_inc_ref(x_443);
x_444 = lean_ctor_get(x_442, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_442, 3);
lean_inc(x_445);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 lean_ctor_release(x_442, 2);
 lean_ctor_release(x_442, 3);
 x_446 = x_442;
} else {
 lean_dec_ref(x_442);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(0, 4, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_441);
lean_ctor_set(x_447, 1, x_443);
lean_ctor_set(x_447, 2, x_444);
lean_ctor_set(x_447, 3, x_445);
x_448 = lean_st_ref_set(x_3, x_447);
lean_dec(x_3);
if (lean_is_scalar(x_439)) {
 x_449 = lean_alloc_ctor(0, 1, 0);
} else {
 x_449 = x_439;
}
lean_ctor_set(x_449, 0, x_440);
return x_449;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_3);
x_450 = lean_ctor_get(x_437, 0);
lean_inc(x_450);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 x_451 = x_437;
} else {
 lean_dec_ref(x_437);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 1, 0);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_450);
return x_452;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_liftGoalM___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_liftGoalM___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liftGoalM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_liftGoalM(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instMonadLiftGoalMSearchM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_liftGoalM___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instMonadLiftGoalMSearchM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instMonadLiftGoalMSearchM___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_2);
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_st_ref_get(x_2);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_st_ref_get(x_2);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_st_mk_ref(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_SearchM_run___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_12 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1;
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 2);
x_17 = lean_ctor_get(x_13, 3);
x_18 = lean_ctor_get(x_13, 4);
x_19 = lean_ctor_get(x_13, 1);
lean_dec(x_19);
x_20 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_21 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_15);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_18);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_17);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_16);
lean_ctor_set(x_13, 4, x_25);
lean_ctor_set(x_13, 3, x_26);
lean_ctor_set(x_13, 2, x_27);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_21);
x_29 = l_ReaderT_instMonad___redArg(x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, x_29);
x_31 = l_instMonadControlTOfPure___redArg(x_30);
lean_inc_ref(x_31);
x_32 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_32, 0, x_11);
lean_closure_set(x_32, 1, x_31);
x_33 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_33, 0, x_11);
lean_closure_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_inc_ref(x_34);
x_35 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_35, 0, x_11);
lean_closure_set(x_35, 1, x_34);
x_36 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_36, 0, x_11);
lean_closure_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc_ref(x_37);
x_38 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_38, 0, x_11);
lean_closure_set(x_38, 1, x_37);
x_39 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_39, 0, x_11);
lean_closure_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = !lean_is_exclusive(x_12);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_12, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 2);
x_47 = lean_ctor_get(x_42, 3);
x_48 = lean_ctor_get(x_42, 4);
x_49 = lean_ctor_get(x_42, 1);
lean_dec(x_49);
lean_inc_ref(x_45);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_50, 0, x_45);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_51, 0, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_53, 0, x_48);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_54, 0, x_47);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_55, 0, x_46);
lean_ctor_set(x_42, 4, x_53);
lean_ctor_set(x_42, 3, x_54);
lean_ctor_set(x_42, 2, x_55);
lean_ctor_set(x_42, 1, x_20);
lean_ctor_set(x_42, 0, x_52);
lean_ctor_set(x_12, 1, x_21);
x_56 = l_ReaderT_instMonad___redArg(x_12);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_61 = lean_ctor_get(x_58, 0);
x_62 = lean_ctor_get(x_58, 2);
x_63 = lean_ctor_get(x_58, 3);
x_64 = lean_ctor_get(x_58, 4);
x_65 = lean_ctor_get(x_58, 1);
lean_dec(x_65);
x_66 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_67 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_61);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_68, 0, x_61);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_69, 0, x_61);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_71, 0, x_64);
x_72 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_72, 0, x_63);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_73, 0, x_62);
lean_ctor_set(x_58, 4, x_71);
lean_ctor_set(x_58, 3, x_72);
lean_ctor_set(x_58, 2, x_73);
lean_ctor_set(x_58, 1, x_66);
lean_ctor_set(x_58, 0, x_70);
lean_ctor_set(x_56, 1, x_67);
x_74 = l_ReaderT_instMonad___redArg(x_56);
x_75 = l_ReaderT_instMonad___redArg(x_74);
lean_inc_ref(x_75);
x_76 = l_ReaderT_instMonad___redArg(x_75);
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
x_78 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_78, 0, x_2);
x_79 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_80 = lean_box(0);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_79);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set(x_82, 3, x_81);
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_83, 0, x_82);
x_84 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_84, 0, lean_box(0));
lean_closure_set(x_84, 1, lean_box(0));
lean_closure_set(x_84, 2, x_75);
lean_closure_set(x_84, 3, lean_box(0));
lean_closure_set(x_84, 4, lean_box(0));
lean_closure_set(x_84, 5, x_83);
lean_closure_set(x_84, 6, x_78);
x_85 = l_Lean_MVarId_withContext___redArg(x_40, x_76, x_77, x_84);
x_86 = lean_apply_8(x_85, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_87 = lean_ctor_get(x_58, 0);
x_88 = lean_ctor_get(x_58, 2);
x_89 = lean_ctor_get(x_58, 3);
x_90 = lean_ctor_get(x_58, 4);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_58);
x_91 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_92 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_87);
x_93 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_93, 0, x_87);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_94, 0, x_87);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_90);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_97, 0, x_89);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_98, 0, x_88);
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_91);
lean_ctor_set(x_99, 2, x_98);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_96);
lean_ctor_set(x_56, 1, x_92);
lean_ctor_set(x_56, 0, x_99);
x_100 = l_ReaderT_instMonad___redArg(x_56);
x_101 = l_ReaderT_instMonad___redArg(x_100);
lean_inc_ref(x_101);
x_102 = l_ReaderT_instMonad___redArg(x_101);
x_103 = lean_ctor_get(x_1, 0);
lean_inc(x_103);
x_104 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_104, 0, x_2);
x_105 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_106 = lean_box(0);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_105);
lean_ctor_set(x_108, 2, x_106);
lean_ctor_set(x_108, 3, x_107);
x_109 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_109, 0, x_108);
x_110 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_110, 0, lean_box(0));
lean_closure_set(x_110, 1, lean_box(0));
lean_closure_set(x_110, 2, x_101);
lean_closure_set(x_110, 3, lean_box(0));
lean_closure_set(x_110, 4, lean_box(0));
lean_closure_set(x_110, 5, x_109);
lean_closure_set(x_110, 6, x_104);
x_111 = l_Lean_MVarId_withContext___redArg(x_40, x_102, x_103, x_110);
x_112 = lean_apply_8(x_111, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_113 = lean_ctor_get(x_56, 0);
lean_inc(x_113);
lean_dec(x_56);
x_114 = lean_ctor_get(x_113, 0);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_113, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 4);
lean_inc(x_117);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_118 = x_113;
} else {
 lean_dec_ref(x_113);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_120 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_114);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_121, 0, x_114);
x_122 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_122, 0, x_114);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_124, 0, x_117);
x_125 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_125, 0, x_116);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_126, 0, x_115);
if (lean_is_scalar(x_118)) {
 x_127 = lean_alloc_ctor(0, 5, 0);
} else {
 x_127 = x_118;
}
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_125);
lean_ctor_set(x_127, 4, x_124);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_120);
x_129 = l_ReaderT_instMonad___redArg(x_128);
x_130 = l_ReaderT_instMonad___redArg(x_129);
lean_inc_ref(x_130);
x_131 = l_ReaderT_instMonad___redArg(x_130);
x_132 = lean_ctor_get(x_1, 0);
lean_inc(x_132);
x_133 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_133, 0, x_2);
x_134 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_135 = lean_box(0);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_136);
x_138 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_138, 0, x_137);
x_139 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_139, 0, lean_box(0));
lean_closure_set(x_139, 1, lean_box(0));
lean_closure_set(x_139, 2, x_130);
lean_closure_set(x_139, 3, lean_box(0));
lean_closure_set(x_139, 4, lean_box(0));
lean_closure_set(x_139, 5, x_138);
lean_closure_set(x_139, 6, x_133);
x_140 = l_Lean_MVarId_withContext___redArg(x_40, x_131, x_132, x_139);
x_141 = lean_apply_8(x_140, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_142 = lean_ctor_get(x_42, 0);
x_143 = lean_ctor_get(x_42, 2);
x_144 = lean_ctor_get(x_42, 3);
x_145 = lean_ctor_get(x_42, 4);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_42);
lean_inc_ref(x_142);
x_146 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_146, 0, x_142);
x_147 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_147, 0, x_142);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_149, 0, x_145);
x_150 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_150, 0, x_144);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_151, 0, x_143);
x_152 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_20);
lean_ctor_set(x_152, 2, x_151);
lean_ctor_set(x_152, 3, x_150);
lean_ctor_set(x_152, 4, x_149);
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_152);
x_153 = l_ReaderT_instMonad___redArg(x_12);
x_154 = lean_ctor_get(x_153, 0);
lean_inc_ref(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_154, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_154, 4);
lean_inc(x_159);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 lean_ctor_release(x_154, 4);
 x_160 = x_154;
} else {
 lean_dec_ref(x_154);
 x_160 = lean_box(0);
}
x_161 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_162 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_156);
x_163 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_163, 0, x_156);
x_164 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_164, 0, x_156);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_166, 0, x_159);
x_167 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_167, 0, x_158);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_168, 0, x_157);
if (lean_is_scalar(x_160)) {
 x_169 = lean_alloc_ctor(0, 5, 0);
} else {
 x_169 = x_160;
}
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_161);
lean_ctor_set(x_169, 2, x_168);
lean_ctor_set(x_169, 3, x_167);
lean_ctor_set(x_169, 4, x_166);
if (lean_is_scalar(x_155)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_155;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_162);
x_171 = l_ReaderT_instMonad___redArg(x_170);
x_172 = l_ReaderT_instMonad___redArg(x_171);
lean_inc_ref(x_172);
x_173 = l_ReaderT_instMonad___redArg(x_172);
x_174 = lean_ctor_get(x_1, 0);
lean_inc(x_174);
x_175 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_175, 0, x_2);
x_176 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_177 = lean_box(0);
x_178 = lean_box(0);
x_179 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_179, 0, x_1);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_178);
x_180 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_180, 0, x_179);
x_181 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_181, 0, lean_box(0));
lean_closure_set(x_181, 1, lean_box(0));
lean_closure_set(x_181, 2, x_172);
lean_closure_set(x_181, 3, lean_box(0));
lean_closure_set(x_181, 4, lean_box(0));
lean_closure_set(x_181, 5, x_180);
lean_closure_set(x_181, 6, x_175);
x_182 = l_Lean_MVarId_withContext___redArg(x_40, x_173, x_174, x_181);
x_183 = lean_apply_8(x_182, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_184 = lean_ctor_get(x_12, 0);
lean_inc(x_184);
lean_dec(x_12);
x_185 = lean_ctor_get(x_184, 0);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_184, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 3);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 4);
lean_inc(x_188);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 x_189 = x_184;
} else {
 lean_dec_ref(x_184);
 x_189 = lean_box(0);
}
lean_inc_ref(x_185);
x_190 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_190, 0, x_185);
x_191 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_191, 0, x_185);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_193, 0, x_188);
x_194 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_194, 0, x_187);
x_195 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_195, 0, x_186);
if (lean_is_scalar(x_189)) {
 x_196 = lean_alloc_ctor(0, 5, 0);
} else {
 x_196 = x_189;
}
lean_ctor_set(x_196, 0, x_192);
lean_ctor_set(x_196, 1, x_20);
lean_ctor_set(x_196, 2, x_195);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set(x_196, 4, x_193);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_21);
x_198 = l_ReaderT_instMonad___redArg(x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc_ref(x_199);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_200 = x_198;
} else {
 lean_dec_ref(x_198);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_201);
x_202 = lean_ctor_get(x_199, 2);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 4);
lean_inc(x_204);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 x_205 = x_199;
} else {
 lean_dec_ref(x_199);
 x_205 = lean_box(0);
}
x_206 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_207 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_201);
x_208 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_208, 0, x_201);
x_209 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_209, 0, x_201);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_211, 0, x_204);
x_212 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_212, 0, x_203);
x_213 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_213, 0, x_202);
if (lean_is_scalar(x_205)) {
 x_214 = lean_alloc_ctor(0, 5, 0);
} else {
 x_214 = x_205;
}
lean_ctor_set(x_214, 0, x_210);
lean_ctor_set(x_214, 1, x_206);
lean_ctor_set(x_214, 2, x_213);
lean_ctor_set(x_214, 3, x_212);
lean_ctor_set(x_214, 4, x_211);
if (lean_is_scalar(x_200)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_200;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_207);
x_216 = l_ReaderT_instMonad___redArg(x_215);
x_217 = l_ReaderT_instMonad___redArg(x_216);
lean_inc_ref(x_217);
x_218 = l_ReaderT_instMonad___redArg(x_217);
x_219 = lean_ctor_get(x_1, 0);
lean_inc(x_219);
x_220 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_220, 0, x_2);
x_221 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_222 = lean_box(0);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_224, 0, x_1);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_222);
lean_ctor_set(x_224, 3, x_223);
x_225 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_225, 0, x_224);
x_226 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_226, 0, lean_box(0));
lean_closure_set(x_226, 1, lean_box(0));
lean_closure_set(x_226, 2, x_217);
lean_closure_set(x_226, 3, lean_box(0));
lean_closure_set(x_226, 4, lean_box(0));
lean_closure_set(x_226, 5, x_225);
lean_closure_set(x_226, 6, x_220);
x_227 = l_Lean_MVarId_withContext___redArg(x_40, x_218, x_219, x_226);
x_228 = lean_apply_8(x_227, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_229 = lean_ctor_get(x_13, 0);
x_230 = lean_ctor_get(x_13, 2);
x_231 = lean_ctor_get(x_13, 3);
x_232 = lean_ctor_get(x_13, 4);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_13);
x_233 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_234 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_229);
x_235 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_235, 0, x_229);
x_236 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_236, 0, x_229);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_238, 0, x_232);
x_239 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_239, 0, x_231);
x_240 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_240, 0, x_230);
x_241 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_241, 0, x_237);
lean_ctor_set(x_241, 1, x_233);
lean_ctor_set(x_241, 2, x_240);
lean_ctor_set(x_241, 3, x_239);
lean_ctor_set(x_241, 4, x_238);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_234);
x_243 = l_ReaderT_instMonad___redArg(x_242);
x_244 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_244, 0, lean_box(0));
lean_closure_set(x_244, 1, lean_box(0));
lean_closure_set(x_244, 2, x_243);
x_245 = l_instMonadControlTOfPure___redArg(x_244);
lean_inc_ref(x_245);
x_246 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_246, 0, x_11);
lean_closure_set(x_246, 1, x_245);
x_247 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_247, 0, x_11);
lean_closure_set(x_247, 1, x_245);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
lean_inc_ref(x_248);
x_249 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_249, 0, x_11);
lean_closure_set(x_249, 1, x_248);
x_250 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_250, 0, x_11);
lean_closure_set(x_250, 1, x_248);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
lean_inc_ref(x_251);
x_252 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_252, 0, x_11);
lean_closure_set(x_252, 1, x_251);
x_253 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_253, 0, x_11);
lean_closure_set(x_253, 1, x_251);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_255);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_256 = x_12;
} else {
 lean_dec_ref(x_12);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_255, 0);
lean_inc_ref(x_257);
x_258 = lean_ctor_get(x_255, 2);
lean_inc(x_258);
x_259 = lean_ctor_get(x_255, 3);
lean_inc(x_259);
x_260 = lean_ctor_get(x_255, 4);
lean_inc(x_260);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 lean_ctor_release(x_255, 2);
 lean_ctor_release(x_255, 3);
 lean_ctor_release(x_255, 4);
 x_261 = x_255;
} else {
 lean_dec_ref(x_255);
 x_261 = lean_box(0);
}
lean_inc_ref(x_257);
x_262 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_262, 0, x_257);
x_263 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_263, 0, x_257);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_265, 0, x_260);
x_266 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_266, 0, x_259);
x_267 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_267, 0, x_258);
if (lean_is_scalar(x_261)) {
 x_268 = lean_alloc_ctor(0, 5, 0);
} else {
 x_268 = x_261;
}
lean_ctor_set(x_268, 0, x_264);
lean_ctor_set(x_268, 1, x_233);
lean_ctor_set(x_268, 2, x_267);
lean_ctor_set(x_268, 3, x_266);
lean_ctor_set(x_268, 4, x_265);
if (lean_is_scalar(x_256)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_256;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_234);
x_270 = l_ReaderT_instMonad___redArg(x_269);
x_271 = lean_ctor_get(x_270, 0);
lean_inc_ref(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
x_273 = lean_ctor_get(x_271, 0);
lean_inc_ref(x_273);
x_274 = lean_ctor_get(x_271, 2);
lean_inc(x_274);
x_275 = lean_ctor_get(x_271, 3);
lean_inc(x_275);
x_276 = lean_ctor_get(x_271, 4);
lean_inc(x_276);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 lean_ctor_release(x_271, 4);
 x_277 = x_271;
} else {
 lean_dec_ref(x_271);
 x_277 = lean_box(0);
}
x_278 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_279 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_273);
x_280 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_280, 0, x_273);
x_281 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_281, 0, x_273);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_283, 0, x_276);
x_284 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_284, 0, x_275);
x_285 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_285, 0, x_274);
if (lean_is_scalar(x_277)) {
 x_286 = lean_alloc_ctor(0, 5, 0);
} else {
 x_286 = x_277;
}
lean_ctor_set(x_286, 0, x_282);
lean_ctor_set(x_286, 1, x_278);
lean_ctor_set(x_286, 2, x_285);
lean_ctor_set(x_286, 3, x_284);
lean_ctor_set(x_286, 4, x_283);
if (lean_is_scalar(x_272)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_272;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_279);
x_288 = l_ReaderT_instMonad___redArg(x_287);
x_289 = l_ReaderT_instMonad___redArg(x_288);
lean_inc_ref(x_289);
x_290 = l_ReaderT_instMonad___redArg(x_289);
x_291 = lean_ctor_get(x_1, 0);
lean_inc(x_291);
x_292 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_292, 0, x_2);
x_293 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_294 = lean_box(0);
x_295 = lean_box(0);
x_296 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_296, 0, x_1);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_294);
lean_ctor_set(x_296, 3, x_295);
x_297 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_297, 0, x_296);
x_298 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_298, 0, lean_box(0));
lean_closure_set(x_298, 1, lean_box(0));
lean_closure_set(x_298, 2, x_289);
lean_closure_set(x_298, 3, lean_box(0));
lean_closure_set(x_298, 4, lean_box(0));
lean_closure_set(x_298, 5, x_297);
lean_closure_set(x_298, 6, x_292);
x_299 = l_Lean_MVarId_withContext___redArg(x_254, x_290, x_291, x_298);
x_300 = lean_apply_8(x_299, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_300;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6;
x_13 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1;
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 2);
x_18 = lean_ctor_get(x_14, 3);
x_19 = lean_ctor_get(x_14, 4);
x_20 = lean_ctor_get(x_14, 1);
lean_dec(x_20);
x_21 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_22 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_16);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_17);
lean_ctor_set(x_14, 4, x_26);
lean_ctor_set(x_14, 3, x_27);
lean_ctor_set(x_14, 2, x_28);
lean_ctor_set(x_14, 1, x_21);
lean_ctor_set(x_14, 0, x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_22);
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, lean_box(0));
lean_closure_set(x_31, 2, x_30);
x_32 = l_instMonadControlTOfPure___redArg(x_31);
lean_inc_ref(x_32);
x_33 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_33, 0, x_12);
lean_closure_set(x_33, 1, x_32);
x_34 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_34, 0, x_12);
lean_closure_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc_ref(x_35);
x_36 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_36, 0, x_12);
lean_closure_set(x_36, 1, x_35);
x_37 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_37, 0, x_12);
lean_closure_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_inc_ref(x_38);
x_39 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_39, 0, x_12);
lean_closure_set(x_39, 1, x_38);
x_40 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_40, 0, x_12);
lean_closure_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 2);
x_48 = lean_ctor_get(x_43, 3);
x_49 = lean_ctor_get(x_43, 4);
x_50 = lean_ctor_get(x_43, 1);
lean_dec(x_50);
lean_inc_ref(x_46);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_51, 0, x_46);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_52, 0, x_46);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_54, 0, x_49);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_55, 0, x_48);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_56, 0, x_47);
lean_ctor_set(x_43, 4, x_54);
lean_ctor_set(x_43, 3, x_55);
lean_ctor_set(x_43, 2, x_56);
lean_ctor_set(x_43, 1, x_21);
lean_ctor_set(x_43, 0, x_53);
lean_ctor_set(x_13, 1, x_22);
x_57 = l_ReaderT_instMonad___redArg(x_13);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_ctor_get(x_59, 2);
x_64 = lean_ctor_get(x_59, 3);
x_65 = lean_ctor_get(x_59, 4);
x_66 = lean_ctor_get(x_59, 1);
lean_dec(x_66);
x_67 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_68 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_62);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_69, 0, x_62);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_70, 0, x_62);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_72, 0, x_65);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_73, 0, x_64);
x_74 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_74, 0, x_63);
lean_ctor_set(x_59, 4, x_72);
lean_ctor_set(x_59, 3, x_73);
lean_ctor_set(x_59, 2, x_74);
lean_ctor_set(x_59, 1, x_67);
lean_ctor_set(x_59, 0, x_71);
lean_ctor_set(x_57, 1, x_68);
x_75 = l_ReaderT_instMonad___redArg(x_57);
x_76 = l_ReaderT_instMonad___redArg(x_75);
lean_inc_ref(x_76);
x_77 = l_ReaderT_instMonad___redArg(x_76);
x_78 = lean_ctor_get(x_2, 0);
lean_inc(x_78);
x_79 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_79, 0, x_3);
x_80 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_81 = lean_box(0);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_2);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_82);
x_84 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_84, 0, x_83);
x_85 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_85, 0, lean_box(0));
lean_closure_set(x_85, 1, lean_box(0));
lean_closure_set(x_85, 2, x_76);
lean_closure_set(x_85, 3, lean_box(0));
lean_closure_set(x_85, 4, lean_box(0));
lean_closure_set(x_85, 5, x_84);
lean_closure_set(x_85, 6, x_79);
x_86 = l_Lean_MVarId_withContext___redArg(x_41, x_77, x_78, x_85);
x_87 = lean_apply_8(x_86, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_88 = lean_ctor_get(x_59, 0);
x_89 = lean_ctor_get(x_59, 2);
x_90 = lean_ctor_get(x_59, 3);
x_91 = lean_ctor_get(x_59, 4);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_59);
x_92 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_93 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_88);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_94, 0, x_88);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_95, 0, x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_97, 0, x_91);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_98, 0, x_90);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_99, 0, x_89);
x_100 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_92);
lean_ctor_set(x_100, 2, x_99);
lean_ctor_set(x_100, 3, x_98);
lean_ctor_set(x_100, 4, x_97);
lean_ctor_set(x_57, 1, x_93);
lean_ctor_set(x_57, 0, x_100);
x_101 = l_ReaderT_instMonad___redArg(x_57);
x_102 = l_ReaderT_instMonad___redArg(x_101);
lean_inc_ref(x_102);
x_103 = l_ReaderT_instMonad___redArg(x_102);
x_104 = lean_ctor_get(x_2, 0);
lean_inc(x_104);
x_105 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_105, 0, x_3);
x_106 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_107 = lean_box(0);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_2);
lean_ctor_set(x_109, 1, x_106);
lean_ctor_set(x_109, 2, x_107);
lean_ctor_set(x_109, 3, x_108);
x_110 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_110, 0, x_109);
x_111 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_111, 0, lean_box(0));
lean_closure_set(x_111, 1, lean_box(0));
lean_closure_set(x_111, 2, x_102);
lean_closure_set(x_111, 3, lean_box(0));
lean_closure_set(x_111, 4, lean_box(0));
lean_closure_set(x_111, 5, x_110);
lean_closure_set(x_111, 6, x_105);
x_112 = l_Lean_MVarId_withContext___redArg(x_41, x_103, x_104, x_111);
x_113 = lean_apply_8(x_112, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_114 = lean_ctor_get(x_57, 0);
lean_inc(x_114);
lean_dec(x_57);
x_115 = lean_ctor_get(x_114, 0);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_114, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 4);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_121 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_115);
x_122 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_122, 0, x_115);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_123, 0, x_115);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_125, 0, x_118);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_126, 0, x_117);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_127, 0, x_116);
if (lean_is_scalar(x_119)) {
 x_128 = lean_alloc_ctor(0, 5, 0);
} else {
 x_128 = x_119;
}
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_120);
lean_ctor_set(x_128, 2, x_127);
lean_ctor_set(x_128, 3, x_126);
lean_ctor_set(x_128, 4, x_125);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_121);
x_130 = l_ReaderT_instMonad___redArg(x_129);
x_131 = l_ReaderT_instMonad___redArg(x_130);
lean_inc_ref(x_131);
x_132 = l_ReaderT_instMonad___redArg(x_131);
x_133 = lean_ctor_get(x_2, 0);
lean_inc(x_133);
x_134 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_134, 0, x_3);
x_135 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_136 = lean_box(0);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_135);
lean_ctor_set(x_138, 2, x_136);
lean_ctor_set(x_138, 3, x_137);
x_139 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_139, 0, x_138);
x_140 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_140, 0, lean_box(0));
lean_closure_set(x_140, 1, lean_box(0));
lean_closure_set(x_140, 2, x_131);
lean_closure_set(x_140, 3, lean_box(0));
lean_closure_set(x_140, 4, lean_box(0));
lean_closure_set(x_140, 5, x_139);
lean_closure_set(x_140, 6, x_134);
x_141 = l_Lean_MVarId_withContext___redArg(x_41, x_132, x_133, x_140);
x_142 = lean_apply_8(x_141, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_143 = lean_ctor_get(x_43, 0);
x_144 = lean_ctor_get(x_43, 2);
x_145 = lean_ctor_get(x_43, 3);
x_146 = lean_ctor_get(x_43, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_43);
lean_inc_ref(x_143);
x_147 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_147, 0, x_143);
x_148 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_148, 0, x_143);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_150, 0, x_146);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_151, 0, x_145);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_152, 0, x_144);
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_21);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_153, 3, x_151);
lean_ctor_set(x_153, 4, x_150);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_153);
x_154 = l_ReaderT_instMonad___redArg(x_13);
x_155 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_155, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_155, 4);
lean_inc(x_160);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 lean_ctor_release(x_155, 4);
 x_161 = x_155;
} else {
 lean_dec_ref(x_155);
 x_161 = lean_box(0);
}
x_162 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_163 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_157);
x_164 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_164, 0, x_157);
x_165 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_165, 0, x_157);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_167, 0, x_160);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_168, 0, x_159);
x_169 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_169, 0, x_158);
if (lean_is_scalar(x_161)) {
 x_170 = lean_alloc_ctor(0, 5, 0);
} else {
 x_170 = x_161;
}
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_162);
lean_ctor_set(x_170, 2, x_169);
lean_ctor_set(x_170, 3, x_168);
lean_ctor_set(x_170, 4, x_167);
if (lean_is_scalar(x_156)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_156;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_163);
x_172 = l_ReaderT_instMonad___redArg(x_171);
x_173 = l_ReaderT_instMonad___redArg(x_172);
lean_inc_ref(x_173);
x_174 = l_ReaderT_instMonad___redArg(x_173);
x_175 = lean_ctor_get(x_2, 0);
lean_inc(x_175);
x_176 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_176, 0, x_3);
x_177 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_178 = lean_box(0);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_180, 0, x_2);
lean_ctor_set(x_180, 1, x_177);
lean_ctor_set(x_180, 2, x_178);
lean_ctor_set(x_180, 3, x_179);
x_181 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_181, 0, x_180);
x_182 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_182, 0, lean_box(0));
lean_closure_set(x_182, 1, lean_box(0));
lean_closure_set(x_182, 2, x_173);
lean_closure_set(x_182, 3, lean_box(0));
lean_closure_set(x_182, 4, lean_box(0));
lean_closure_set(x_182, 5, x_181);
lean_closure_set(x_182, 6, x_176);
x_183 = l_Lean_MVarId_withContext___redArg(x_41, x_174, x_175, x_182);
x_184 = lean_apply_8(x_183, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_185 = lean_ctor_get(x_13, 0);
lean_inc(x_185);
lean_dec(x_13);
x_186 = lean_ctor_get(x_185, 0);
lean_inc_ref(x_186);
x_187 = lean_ctor_get(x_185, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 4);
lean_inc(x_189);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 lean_ctor_release(x_185, 4);
 x_190 = x_185;
} else {
 lean_dec_ref(x_185);
 x_190 = lean_box(0);
}
lean_inc_ref(x_186);
x_191 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_191, 0, x_186);
x_192 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_192, 0, x_186);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_194, 0, x_189);
x_195 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_195, 0, x_188);
x_196 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_196, 0, x_187);
if (lean_is_scalar(x_190)) {
 x_197 = lean_alloc_ctor(0, 5, 0);
} else {
 x_197 = x_190;
}
lean_ctor_set(x_197, 0, x_193);
lean_ctor_set(x_197, 1, x_21);
lean_ctor_set(x_197, 2, x_196);
lean_ctor_set(x_197, 3, x_195);
lean_ctor_set(x_197, 4, x_194);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_22);
x_199 = l_ReaderT_instMonad___redArg(x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_200);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_201 = x_199;
} else {
 lean_dec_ref(x_199);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_200, 0);
lean_inc_ref(x_202);
x_203 = lean_ctor_get(x_200, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 4);
lean_inc(x_205);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 x_206 = x_200;
} else {
 lean_dec_ref(x_200);
 x_206 = lean_box(0);
}
x_207 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_208 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_202);
x_209 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_209, 0, x_202);
x_210 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_210, 0, x_202);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_212, 0, x_205);
x_213 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_213, 0, x_204);
x_214 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_214, 0, x_203);
if (lean_is_scalar(x_206)) {
 x_215 = lean_alloc_ctor(0, 5, 0);
} else {
 x_215 = x_206;
}
lean_ctor_set(x_215, 0, x_211);
lean_ctor_set(x_215, 1, x_207);
lean_ctor_set(x_215, 2, x_214);
lean_ctor_set(x_215, 3, x_213);
lean_ctor_set(x_215, 4, x_212);
if (lean_is_scalar(x_201)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_201;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_208);
x_217 = l_ReaderT_instMonad___redArg(x_216);
x_218 = l_ReaderT_instMonad___redArg(x_217);
lean_inc_ref(x_218);
x_219 = l_ReaderT_instMonad___redArg(x_218);
x_220 = lean_ctor_get(x_2, 0);
lean_inc(x_220);
x_221 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_221, 0, x_3);
x_222 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_223 = lean_box(0);
x_224 = lean_box(0);
x_225 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_225, 0, x_2);
lean_ctor_set(x_225, 1, x_222);
lean_ctor_set(x_225, 2, x_223);
lean_ctor_set(x_225, 3, x_224);
x_226 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_226, 0, x_225);
x_227 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_227, 0, lean_box(0));
lean_closure_set(x_227, 1, lean_box(0));
lean_closure_set(x_227, 2, x_218);
lean_closure_set(x_227, 3, lean_box(0));
lean_closure_set(x_227, 4, lean_box(0));
lean_closure_set(x_227, 5, x_226);
lean_closure_set(x_227, 6, x_221);
x_228 = l_Lean_MVarId_withContext___redArg(x_41, x_219, x_220, x_227);
x_229 = lean_apply_8(x_228, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_230 = lean_ctor_get(x_14, 0);
x_231 = lean_ctor_get(x_14, 2);
x_232 = lean_ctor_get(x_14, 3);
x_233 = lean_ctor_get(x_14, 4);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_14);
x_234 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_235 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_230);
x_236 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_236, 0, x_230);
x_237 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_237, 0, x_230);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
x_239 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_239, 0, x_233);
x_240 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_240, 0, x_232);
x_241 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_241, 0, x_231);
x_242 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_242, 0, x_238);
lean_ctor_set(x_242, 1, x_234);
lean_ctor_set(x_242, 2, x_241);
lean_ctor_set(x_242, 3, x_240);
lean_ctor_set(x_242, 4, x_239);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_235);
x_244 = l_ReaderT_instMonad___redArg(x_243);
x_245 = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(x_245, 0, lean_box(0));
lean_closure_set(x_245, 1, lean_box(0));
lean_closure_set(x_245, 2, x_244);
x_246 = l_instMonadControlTOfPure___redArg(x_245);
lean_inc_ref(x_246);
x_247 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_247, 0, x_12);
lean_closure_set(x_247, 1, x_246);
x_248 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_248, 0, x_12);
lean_closure_set(x_248, 1, x_246);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
lean_inc_ref(x_249);
x_250 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_250, 0, x_12);
lean_closure_set(x_250, 1, x_249);
x_251 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_251, 0, x_12);
lean_closure_set(x_251, 1, x_249);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
lean_inc_ref(x_252);
x_253 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_253, 0, x_12);
lean_closure_set(x_253, 1, x_252);
x_254 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_254, 0, x_12);
lean_closure_set(x_254, 1, x_252);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_256);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_257 = x_13;
} else {
 lean_dec_ref(x_13);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_256, 0);
lean_inc_ref(x_258);
x_259 = lean_ctor_get(x_256, 2);
lean_inc(x_259);
x_260 = lean_ctor_get(x_256, 3);
lean_inc(x_260);
x_261 = lean_ctor_get(x_256, 4);
lean_inc(x_261);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 lean_ctor_release(x_256, 3);
 lean_ctor_release(x_256, 4);
 x_262 = x_256;
} else {
 lean_dec_ref(x_256);
 x_262 = lean_box(0);
}
lean_inc_ref(x_258);
x_263 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_263, 0, x_258);
x_264 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_264, 0, x_258);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_266, 0, x_261);
x_267 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_267, 0, x_260);
x_268 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_268, 0, x_259);
if (lean_is_scalar(x_262)) {
 x_269 = lean_alloc_ctor(0, 5, 0);
} else {
 x_269 = x_262;
}
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_234);
lean_ctor_set(x_269, 2, x_268);
lean_ctor_set(x_269, 3, x_267);
lean_ctor_set(x_269, 4, x_266);
if (lean_is_scalar(x_257)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_257;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_235);
x_271 = l_ReaderT_instMonad___redArg(x_270);
x_272 = lean_ctor_get(x_271, 0);
lean_inc_ref(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_272, 0);
lean_inc_ref(x_274);
x_275 = lean_ctor_get(x_272, 2);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 3);
lean_inc(x_276);
x_277 = lean_ctor_get(x_272, 4);
lean_inc(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 lean_ctor_release(x_272, 4);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
x_279 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_280 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_274);
x_281 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_281, 0, x_274);
x_282 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_282, 0, x_274);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_284, 0, x_277);
x_285 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_285, 0, x_276);
x_286 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_286, 0, x_275);
if (lean_is_scalar(x_278)) {
 x_287 = lean_alloc_ctor(0, 5, 0);
} else {
 x_287 = x_278;
}
lean_ctor_set(x_287, 0, x_283);
lean_ctor_set(x_287, 1, x_279);
lean_ctor_set(x_287, 2, x_286);
lean_ctor_set(x_287, 3, x_285);
lean_ctor_set(x_287, 4, x_284);
if (lean_is_scalar(x_273)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_273;
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_280);
x_289 = l_ReaderT_instMonad___redArg(x_288);
x_290 = l_ReaderT_instMonad___redArg(x_289);
lean_inc_ref(x_290);
x_291 = l_ReaderT_instMonad___redArg(x_290);
x_292 = lean_ctor_get(x_2, 0);
lean_inc(x_292);
x_293 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed), 10, 1);
lean_closure_set(x_293, 0, x_3);
x_294 = l_Lean_Meta_Grind_SearchM_run___redArg___closed__0;
x_295 = lean_box(0);
x_296 = lean_box(0);
x_297 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_297, 0, x_2);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_296);
x_298 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed), 9, 1);
lean_closure_set(x_298, 0, x_297);
x_299 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_299, 0, lean_box(0));
lean_closure_set(x_299, 1, lean_box(0));
lean_closure_set(x_299, 2, x_290);
lean_closure_set(x_299, 3, lean_box(0));
lean_closure_set(x_299, 4, lean_box(0));
lean_closure_set(x_299, 5, x_298);
lean_closure_set(x_299, 6, x_293);
x_300 = l_Lean_MVarId_withContext___redArg(x_255, x_291, x_292, x_299);
x_301 = lean_apply_8(x_300, x_4, x_5, x_6, x_7, x_8, x_9, x_10, lean_box(0));
return x_301;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_SearchM_run___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_SearchM_run___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_SearchM_run___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_SearchM_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_SearchM_run(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l_Lean_instBEqMVarId_beq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l_Lean_instBEqMVarId_beq(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1_spec__1___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_instHashableMVarId_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l_Lean_instBEqMVarId_beq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l_Lean_instBEqMVarId_beq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__2;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__1___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__2;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_instHashableMVarId_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_st_ref_get(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = lean_st_mk_ref(x_13);
x_15 = lean_st_ref_take(x_8);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 7);
x_20 = l_Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1___redArg(x_19, x_1, x_2);
lean_ctor_set(x_17, 7, x_20);
x_21 = lean_st_ref_set(x_8, x_15);
x_22 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
x_28 = lean_ctor_get(x_17, 2);
x_29 = lean_ctor_get(x_17, 3);
x_30 = lean_ctor_get(x_17, 4);
x_31 = lean_ctor_get(x_17, 5);
x_32 = lean_ctor_get(x_17, 6);
x_33 = lean_ctor_get(x_17, 7);
x_34 = lean_ctor_get(x_17, 8);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_35 = l_Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1___redArg(x_33, x_1, x_2);
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_27);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_36, 3, x_29);
lean_ctor_set(x_36, 4, x_30);
lean_ctor_set(x_36, 5, x_31);
lean_ctor_set(x_36, 6, x_32);
lean_ctor_set(x_36, 7, x_35);
lean_ctor_set(x_36, 8, x_34);
lean_ctor_set(x_15, 0, x_36);
x_37 = lean_st_ref_set(x_8, x_15);
x_38 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
x_44 = lean_ctor_get(x_15, 2);
x_45 = lean_ctor_get(x_15, 3);
x_46 = lean_ctor_get(x_15, 4);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 3);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_42, 4);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_42, 5);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_42, 6);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_42, 7);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_42, 8);
lean_inc_ref(x_55);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 lean_ctor_release(x_42, 4);
 lean_ctor_release(x_42, 5);
 lean_ctor_release(x_42, 6);
 lean_ctor_release(x_42, 7);
 lean_ctor_release(x_42, 8);
 x_56 = x_42;
} else {
 lean_dec_ref(x_42);
 x_56 = lean_box(0);
}
x_57 = l_Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1___redArg(x_54, x_1, x_2);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 9, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_47);
lean_ctor_set(x_58, 1, x_48);
lean_ctor_set(x_58, 2, x_49);
lean_ctor_set(x_58, 3, x_50);
lean_ctor_set(x_58, 4, x_51);
lean_ctor_set(x_58, 5, x_52);
lean_ctor_set(x_58, 6, x_53);
lean_ctor_set(x_58, 7, x_57);
lean_ctor_set(x_58, 8, x_55);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_59, 2, x_44);
lean_ctor_set(x_59, 3, x_45);
lean_ctor_set(x_59, 4, x_46);
x_60 = lean_st_ref_set(x_8, x_59);
x_61 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1___lam__0___boxed), 11, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_inc(x_3);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_20);
x_24 = lean_st_ref_set(x_3, x_21);
lean_dec(x_3);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_21, 2);
x_27 = lean_ctor_get(x_21, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_27);
x_29 = lean_st_ref_set(x_3, x_28);
lean_dec(x_3);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_take(x_3);
x_34 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 3);
lean_inc(x_36);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 x_37 = x_33;
} else {
 lean_dec_ref(x_33);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 4, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
x_39 = lean_st_ref_set(x_3, x_38);
lean_dec(x_3);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_31);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_16, 0);
lean_inc(x_42);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_mkChoice_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 4);
x_20 = lean_ctor_get(x_13, 1);
lean_dec(x_20);
x_21 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_22 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_16);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_17);
lean_ctor_set(x_13, 4, x_26);
lean_ctor_set(x_13, 3, x_27);
lean_ctor_set(x_13, 2, x_28);
lean_ctor_set(x_13, 1, x_21);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_11, 1, x_22);
x_29 = l_ReaderT_instMonad___redArg(x_11);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_38 = lean_ctor_get(x_31, 1);
lean_dec(x_38);
x_39 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_40 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_36);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_35);
lean_ctor_set(x_31, 4, x_44);
lean_ctor_set(x_31, 3, x_45);
lean_ctor_set(x_31, 2, x_46);
lean_ctor_set(x_31, 1, x_39);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_29, 1, x_40);
x_47 = l_ReaderT_instMonad___redArg(x_29);
x_48 = l_ReaderT_instMonad___redArg(x_47);
x_49 = l_ReaderT_instMonad___redArg(x_48);
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = lean_box(0);
x_52 = l_instInhabitedOfMonad___redArg(x_50, x_51);
x_53 = lean_panic_fn(x_52, x_1);
x_54 = lean_apply_9(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_55 = lean_ctor_get(x_31, 0);
x_56 = lean_ctor_get(x_31, 2);
x_57 = lean_ctor_get(x_31, 3);
x_58 = lean_ctor_get(x_31, 4);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_31);
x_59 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_60 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_55);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_61, 0, x_55);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_62, 0, x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_64, 0, x_58);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_65, 0, x_57);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_66, 0, x_56);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_65);
lean_ctor_set(x_67, 4, x_64);
lean_ctor_set(x_29, 1, x_60);
lean_ctor_set(x_29, 0, x_67);
x_68 = l_ReaderT_instMonad___redArg(x_29);
x_69 = l_ReaderT_instMonad___redArg(x_68);
x_70 = l_ReaderT_instMonad___redArg(x_69);
x_71 = l_ReaderT_instMonad___redArg(x_70);
x_72 = lean_box(0);
x_73 = l_instInhabitedOfMonad___redArg(x_71, x_72);
x_74 = lean_panic_fn(x_73, x_1);
x_75 = lean_apply_9(x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_76 = lean_ctor_get(x_29, 0);
lean_inc(x_76);
lean_dec(x_29);
x_77 = lean_ctor_get(x_76, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_76, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 4);
lean_inc(x_80);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 lean_ctor_release(x_76, 4);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
x_82 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_83 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_77);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_84, 0, x_77);
x_85 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_85, 0, x_77);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_87, 0, x_80);
x_88 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_88, 0, x_79);
x_89 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_89, 0, x_78);
if (lean_is_scalar(x_81)) {
 x_90 = lean_alloc_ctor(0, 5, 0);
} else {
 x_90 = x_81;
}
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_82);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_88);
lean_ctor_set(x_90, 4, x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
x_92 = l_ReaderT_instMonad___redArg(x_91);
x_93 = l_ReaderT_instMonad___redArg(x_92);
x_94 = l_ReaderT_instMonad___redArg(x_93);
x_95 = l_ReaderT_instMonad___redArg(x_94);
x_96 = lean_box(0);
x_97 = l_instInhabitedOfMonad___redArg(x_95, x_96);
x_98 = lean_panic_fn(x_97, x_1);
x_99 = lean_apply_9(x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_100 = lean_ctor_get(x_13, 0);
x_101 = lean_ctor_get(x_13, 2);
x_102 = lean_ctor_get(x_13, 3);
x_103 = lean_ctor_get(x_13, 4);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_13);
x_104 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_105 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_100);
x_106 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_106, 0, x_100);
x_107 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_107, 0, x_100);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_109, 0, x_103);
x_110 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_110, 0, x_102);
x_111 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_111, 0, x_101);
x_112 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_104);
lean_ctor_set(x_112, 2, x_111);
lean_ctor_set(x_112, 3, x_110);
lean_ctor_set(x_112, 4, x_109);
lean_ctor_set(x_11, 1, x_105);
lean_ctor_set(x_11, 0, x_112);
x_113 = l_ReaderT_instMonad___redArg(x_11);
x_114 = lean_ctor_get(x_113, 0);
lean_inc_ref(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_114, 0);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_114, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 4);
lean_inc(x_119);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_120 = x_114;
} else {
 lean_dec_ref(x_114);
 x_120 = lean_box(0);
}
x_121 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_122 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_116);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_123, 0, x_116);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_124, 0, x_116);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_126, 0, x_119);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_127, 0, x_118);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_128, 0, x_117);
if (lean_is_scalar(x_120)) {
 x_129 = lean_alloc_ctor(0, 5, 0);
} else {
 x_129 = x_120;
}
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_121);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_127);
lean_ctor_set(x_129, 4, x_126);
if (lean_is_scalar(x_115)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_115;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_122);
x_131 = l_ReaderT_instMonad___redArg(x_130);
x_132 = l_ReaderT_instMonad___redArg(x_131);
x_133 = l_ReaderT_instMonad___redArg(x_132);
x_134 = l_ReaderT_instMonad___redArg(x_133);
x_135 = lean_box(0);
x_136 = l_instInhabitedOfMonad___redArg(x_134, x_135);
x_137 = lean_panic_fn(x_136, x_1);
x_138 = lean_apply_9(x_137, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_139 = lean_ctor_get(x_11, 0);
lean_inc(x_139);
lean_dec(x_11);
x_140 = lean_ctor_get(x_139, 0);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_139, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 4);
lean_inc(x_143);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 lean_ctor_release(x_139, 2);
 lean_ctor_release(x_139, 3);
 lean_ctor_release(x_139, 4);
 x_144 = x_139;
} else {
 lean_dec_ref(x_139);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_146 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_140);
x_147 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_147, 0, x_140);
x_148 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_148, 0, x_140);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_150, 0, x_143);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_151, 0, x_142);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_152, 0, x_141);
if (lean_is_scalar(x_144)) {
 x_153 = lean_alloc_ctor(0, 5, 0);
} else {
 x_153 = x_144;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_145);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_153, 3, x_151);
lean_ctor_set(x_153, 4, x_150);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_146);
x_155 = l_ReaderT_instMonad___redArg(x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_158);
x_159 = lean_ctor_get(x_156, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_156, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_156, 4);
lean_inc(x_161);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 lean_ctor_release(x_156, 3);
 lean_ctor_release(x_156, 4);
 x_162 = x_156;
} else {
 lean_dec_ref(x_156);
 x_162 = lean_box(0);
}
x_163 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_164 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_158);
x_165 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_165, 0, x_158);
x_166 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_166, 0, x_158);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_168, 0, x_161);
x_169 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_169, 0, x_160);
x_170 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_170, 0, x_159);
if (lean_is_scalar(x_162)) {
 x_171 = lean_alloc_ctor(0, 5, 0);
} else {
 x_171 = x_162;
}
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_170);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set(x_171, 4, x_168);
if (lean_is_scalar(x_157)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_157;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_164);
x_173 = l_ReaderT_instMonad___redArg(x_172);
x_174 = l_ReaderT_instMonad___redArg(x_173);
x_175 = l_ReaderT_instMonad___redArg(x_174);
x_176 = l_ReaderT_instMonad___redArg(x_175);
x_177 = lean_box(0);
x_178 = l_instInhabitedOfMonad___redArg(x_176, x_177);
x_179 = lean_panic_fn(x_178, x_1);
x_180 = lean_apply_9(x_179, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_180;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_st_ref_get(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = lean_st_mk_ref(x_11);
x_13 = l_Lean_Meta_Grind_isInconsistent___redArg(x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_st_ref_get(x_12);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_st_ref_get(x_12);
lean_dec(x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.SearchM", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.mkChoice", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: !( __do_lift._@.Lean.Meta.Tactic.Grind.SearchM.318984621._hygCtx._hyg.17.0 )\n  ", 100, 100);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkChoice___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_mkChoice___closed__3;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(89u);
x_4 = l_Lean_Meta_Grind_mkChoice___closed__2;
x_5 = l_Lean_Meta_Grind_mkChoice___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Meta_Grind_getGoal___redArg(x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkChoice___lam__0___boxed), 9, 0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_take(x_5);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_21);
x_25 = lean_st_ref_set(x_5, x_22);
x_26 = lean_unbox(x_20);
lean_dec(x_20);
if (x_26 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
lean_dec(x_3);
x_27 = l_Lean_Meta_Grind_getGoal___redArg(x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_5);
x_30 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_29, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_st_ref_take(x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 1;
lean_ctor_set_uint8(x_35, sizeof(void*)*17, x_37);
x_38 = lean_st_ref_set(x_5, x_33);
lean_dec(x_5);
x_39 = lean_box(0);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
x_42 = lean_ctor_get(x_35, 2);
x_43 = lean_ctor_get(x_35, 3);
x_44 = lean_ctor_get(x_35, 4);
x_45 = lean_ctor_get(x_35, 5);
x_46 = lean_ctor_get(x_35, 6);
x_47 = lean_ctor_get(x_35, 7);
x_48 = lean_ctor_get(x_35, 8);
x_49 = lean_ctor_get(x_35, 9);
x_50 = lean_ctor_get(x_35, 10);
x_51 = lean_ctor_get(x_35, 11);
x_52 = lean_ctor_get(x_35, 12);
x_53 = lean_ctor_get(x_35, 13);
x_54 = lean_ctor_get(x_35, 14);
x_55 = lean_ctor_get(x_35, 15);
x_56 = lean_ctor_get(x_35, 16);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_57 = 1;
x_58 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_58, 0, x_40);
lean_ctor_set(x_58, 1, x_41);
lean_ctor_set(x_58, 2, x_42);
lean_ctor_set(x_58, 3, x_43);
lean_ctor_set(x_58, 4, x_44);
lean_ctor_set(x_58, 5, x_45);
lean_ctor_set(x_58, 6, x_46);
lean_ctor_set(x_58, 7, x_47);
lean_ctor_set(x_58, 8, x_48);
lean_ctor_set(x_58, 9, x_49);
lean_ctor_set(x_58, 10, x_50);
lean_ctor_set(x_58, 11, x_51);
lean_ctor_set(x_58, 12, x_52);
lean_ctor_set(x_58, 13, x_53);
lean_ctor_set(x_58, 14, x_54);
lean_ctor_set(x_58, 15, x_55);
lean_ctor_set(x_58, 16, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*17, x_57);
lean_ctor_set(x_33, 0, x_58);
x_59 = lean_st_ref_set(x_5, x_33);
lean_dec(x_5);
x_60 = lean_box(0);
lean_ctor_set(x_30, 0, x_60);
return x_30;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_61 = lean_ctor_get(x_33, 0);
x_62 = lean_ctor_get(x_33, 1);
x_63 = lean_ctor_get(x_33, 2);
x_64 = lean_ctor_get(x_33, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_33);
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_61, 2);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_61, 3);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_61, 4);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_61, 5);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_61, 6);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_61, 7);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_61, 8);
lean_inc(x_73);
x_74 = lean_ctor_get(x_61, 9);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_61, 10);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_61, 11);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_61, 12);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_61, 13);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_61, 14);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_61, 15);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_61, 16);
lean_inc_ref(x_81);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 lean_ctor_release(x_61, 4);
 lean_ctor_release(x_61, 5);
 lean_ctor_release(x_61, 6);
 lean_ctor_release(x_61, 7);
 lean_ctor_release(x_61, 8);
 lean_ctor_release(x_61, 9);
 lean_ctor_release(x_61, 10);
 lean_ctor_release(x_61, 11);
 lean_ctor_release(x_61, 12);
 lean_ctor_release(x_61, 13);
 lean_ctor_release(x_61, 14);
 lean_ctor_release(x_61, 15);
 lean_ctor_release(x_61, 16);
 x_82 = x_61;
} else {
 lean_dec_ref(x_61);
 x_82 = lean_box(0);
}
x_83 = 1;
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 17, 1);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_65);
lean_ctor_set(x_84, 1, x_66);
lean_ctor_set(x_84, 2, x_67);
lean_ctor_set(x_84, 3, x_68);
lean_ctor_set(x_84, 4, x_69);
lean_ctor_set(x_84, 5, x_70);
lean_ctor_set(x_84, 6, x_71);
lean_ctor_set(x_84, 7, x_72);
lean_ctor_set(x_84, 8, x_73);
lean_ctor_set(x_84, 9, x_74);
lean_ctor_set(x_84, 10, x_75);
lean_ctor_set(x_84, 11, x_76);
lean_ctor_set(x_84, 12, x_77);
lean_ctor_set(x_84, 13, x_78);
lean_ctor_set(x_84, 14, x_79);
lean_ctor_set(x_84, 15, x_80);
lean_ctor_set(x_84, 16, x_81);
lean_ctor_set_uint8(x_84, sizeof(void*)*17, x_83);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_62);
lean_ctor_set(x_85, 2, x_63);
lean_ctor_set(x_85, 3, x_64);
x_86 = lean_st_ref_set(x_5, x_85);
lean_dec(x_5);
x_87 = lean_box(0);
lean_ctor_set(x_30, 0, x_87);
return x_30;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_30);
x_88 = lean_st_ref_take(x_5);
x_89 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_88, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 x_93 = x_88;
} else {
 lean_dec_ref(x_88);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_89, 2);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_89, 3);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_89, 4);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_89, 5);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_89, 6);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_89, 7);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_89, 8);
lean_inc(x_102);
x_103 = lean_ctor_get(x_89, 9);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_89, 10);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_89, 11);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_89, 12);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_89, 13);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_89, 14);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_89, 15);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_89, 16);
lean_inc_ref(x_110);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 lean_ctor_release(x_89, 5);
 lean_ctor_release(x_89, 6);
 lean_ctor_release(x_89, 7);
 lean_ctor_release(x_89, 8);
 lean_ctor_release(x_89, 9);
 lean_ctor_release(x_89, 10);
 lean_ctor_release(x_89, 11);
 lean_ctor_release(x_89, 12);
 lean_ctor_release(x_89, 13);
 lean_ctor_release(x_89, 14);
 lean_ctor_release(x_89, 15);
 lean_ctor_release(x_89, 16);
 x_111 = x_89;
} else {
 lean_dec_ref(x_89);
 x_111 = lean_box(0);
}
x_112 = 1;
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 17, 1);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_94);
lean_ctor_set(x_113, 1, x_95);
lean_ctor_set(x_113, 2, x_96);
lean_ctor_set(x_113, 3, x_97);
lean_ctor_set(x_113, 4, x_98);
lean_ctor_set(x_113, 5, x_99);
lean_ctor_set(x_113, 6, x_100);
lean_ctor_set(x_113, 7, x_101);
lean_ctor_set(x_113, 8, x_102);
lean_ctor_set(x_113, 9, x_103);
lean_ctor_set(x_113, 10, x_104);
lean_ctor_set(x_113, 11, x_105);
lean_ctor_set(x_113, 12, x_106);
lean_ctor_set(x_113, 13, x_107);
lean_ctor_set(x_113, 14, x_108);
lean_ctor_set(x_113, 15, x_109);
lean_ctor_set(x_113, 16, x_110);
lean_ctor_set_uint8(x_113, sizeof(void*)*17, x_112);
if (lean_is_scalar(x_93)) {
 x_114 = lean_alloc_ctor(0, 4, 0);
} else {
 x_114 = x_93;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_90);
lean_ctor_set(x_114, 2, x_91);
lean_ctor_set(x_114, 3, x_92);
x_115 = lean_st_ref_set(x_5, x_114);
lean_dec(x_5);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
else
{
lean_dec(x_5);
return x_30;
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_4);
lean_dec(x_3);
x_119 = lean_ctor_get(x_2, 0);
lean_inc(x_119);
lean_dec_ref(x_2);
x_120 = l_Lean_Meta_Grind_getGoal___redArg(x_5);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec(x_121);
lean_inc(x_5);
x_123 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_122, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
lean_dec_ref(x_123);
x_124 = l_Lean_Meta_Grind_setGoal___redArg(x_119, x_5);
lean_dec(x_5);
return x_124;
}
else
{
lean_dec(x_119);
lean_dec(x_5);
return x_123;
}
}
else
{
uint8_t x_125; 
lean_inc_ref(x_118);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_125 = !lean_is_exclusive(x_2);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_2, 0);
x_127 = lean_ctor_get(x_2, 1);
lean_dec(x_127);
x_128 = l_Lean_Meta_Grind_getGoal___redArg(x_5);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_st_ref_take(x_5);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_ctor_get(x_131, 3);
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
x_135 = l_Lean_Meta_Grind_mkChoice___closed__0;
x_136 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_136, 0, x_4);
lean_ctor_set(x_136, 1, x_130);
lean_ctor_set(x_136, 2, x_1);
lean_ctor_set(x_136, 3, x_118);
lean_ctor_set(x_136, 4, x_135);
lean_ctor_set(x_136, 5, x_3);
lean_ctor_set(x_2, 1, x_133);
lean_ctor_set(x_2, 0, x_136);
lean_ctor_set(x_131, 3, x_2);
lean_ctor_set(x_131, 0, x_126);
x_137 = lean_st_ref_set(x_5, x_131);
lean_dec(x_5);
x_138 = lean_box(0);
lean_ctor_set(x_128, 0, x_138);
return x_128;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_131, 1);
x_140 = lean_ctor_get(x_131, 2);
x_141 = lean_ctor_get(x_131, 3);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_131);
x_142 = l_Lean_Meta_Grind_mkChoice___closed__0;
x_143 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_143, 0, x_4);
lean_ctor_set(x_143, 1, x_130);
lean_ctor_set(x_143, 2, x_1);
lean_ctor_set(x_143, 3, x_118);
lean_ctor_set(x_143, 4, x_142);
lean_ctor_set(x_143, 5, x_3);
lean_ctor_set(x_2, 1, x_141);
lean_ctor_set(x_2, 0, x_143);
x_144 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_144, 0, x_126);
lean_ctor_set(x_144, 1, x_139);
lean_ctor_set(x_144, 2, x_140);
lean_ctor_set(x_144, 3, x_2);
x_145 = lean_st_ref_set(x_5, x_144);
lean_dec(x_5);
x_146 = lean_box(0);
lean_ctor_set(x_128, 0, x_146);
return x_128;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_147 = lean_ctor_get(x_128, 0);
lean_inc(x_147);
lean_dec(x_128);
x_148 = lean_st_ref_take(x_5);
x_149 = lean_ctor_get(x_148, 1);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_148, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 3);
lean_inc(x_151);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 x_152 = x_148;
} else {
 lean_dec_ref(x_148);
 x_152 = lean_box(0);
}
x_153 = l_Lean_Meta_Grind_mkChoice___closed__0;
x_154 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_154, 0, x_4);
lean_ctor_set(x_154, 1, x_147);
lean_ctor_set(x_154, 2, x_1);
lean_ctor_set(x_154, 3, x_118);
lean_ctor_set(x_154, 4, x_153);
lean_ctor_set(x_154, 5, x_3);
lean_ctor_set(x_2, 1, x_151);
lean_ctor_set(x_2, 0, x_154);
if (lean_is_scalar(x_152)) {
 x_155 = lean_alloc_ctor(0, 4, 0);
} else {
 x_155 = x_152;
}
lean_ctor_set(x_155, 0, x_126);
lean_ctor_set(x_155, 1, x_149);
lean_ctor_set(x_155, 2, x_150);
lean_ctor_set(x_155, 3, x_2);
x_156 = lean_st_ref_set(x_5, x_155);
lean_dec(x_5);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_159 = lean_ctor_get(x_2, 0);
lean_inc(x_159);
lean_dec(x_2);
x_160 = l_Lean_Meta_Grind_getGoal___redArg(x_5);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_st_ref_take(x_5);
x_164 = lean_ctor_get(x_163, 1);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_163, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 3);
lean_inc(x_166);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 x_167 = x_163;
} else {
 lean_dec_ref(x_163);
 x_167 = lean_box(0);
}
x_168 = l_Lean_Meta_Grind_mkChoice___closed__0;
x_169 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_169, 0, x_4);
lean_ctor_set(x_169, 1, x_161);
lean_ctor_set(x_169, 2, x_1);
lean_ctor_set(x_169, 3, x_118);
lean_ctor_set(x_169, 4, x_168);
lean_ctor_set(x_169, 5, x_3);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
if (lean_is_scalar(x_167)) {
 x_171 = lean_alloc_ctor(0, 4, 0);
} else {
 x_171 = x_167;
}
lean_ctor_set(x_171, 0, x_159);
lean_ctor_set(x_171, 1, x_164);
lean_ctor_set(x_171, 2, x_165);
lean_ctor_set(x_171, 3, x_170);
x_172 = lean_st_ref_set(x_5, x_171);
lean_dec(x_5);
x_173 = lean_box(0);
if (lean_is_scalar(x_162)) {
 x_174 = lean_alloc_ctor(0, 1, 0);
} else {
 x_174 = x_162;
}
lean_ctor_set(x_174, 0, x_173);
return x_174;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_175 = l_Lean_Meta_Grind_mkChoice___closed__4;
x_176 = l_panic___at___Lean_Meta_Grind_mkChoice_spec__7(x_175, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_177 = lean_ctor_get(x_22, 1);
x_178 = lean_ctor_get(x_22, 2);
x_179 = lean_ctor_get(x_22, 3);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_22);
x_180 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_180, 0, x_21);
lean_ctor_set(x_180, 1, x_177);
lean_ctor_set(x_180, 2, x_178);
lean_ctor_set(x_180, 3, x_179);
x_181 = lean_st_ref_set(x_5, x_180);
x_182 = lean_unbox(x_20);
lean_dec(x_20);
if (x_182 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_4);
lean_dec(x_3);
x_183 = l_Lean_Meta_Grind_getGoal___redArg(x_5);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec(x_184);
lean_inc(x_5);
x_186 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_185, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_187 = x_186;
} else {
 lean_dec_ref(x_186);
 x_187 = lean_box(0);
}
x_188 = lean_st_ref_take(x_5);
x_189 = lean_ctor_get(x_188, 0);
lean_inc_ref(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc_ref(x_190);
x_191 = lean_ctor_get(x_188, 2);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 3);
lean_inc(x_192);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_193 = x_188;
} else {
 lean_dec_ref(x_188);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_189, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_189, 1);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_189, 2);
lean_inc_ref(x_196);
x_197 = lean_ctor_get(x_189, 3);
lean_inc_ref(x_197);
x_198 = lean_ctor_get(x_189, 4);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_189, 5);
lean_inc_ref(x_199);
x_200 = lean_ctor_get(x_189, 6);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_189, 7);
lean_inc_ref(x_201);
x_202 = lean_ctor_get(x_189, 8);
lean_inc(x_202);
x_203 = lean_ctor_get(x_189, 9);
lean_inc_ref(x_203);
x_204 = lean_ctor_get(x_189, 10);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_189, 11);
lean_inc_ref(x_205);
x_206 = lean_ctor_get(x_189, 12);
lean_inc_ref(x_206);
x_207 = lean_ctor_get(x_189, 13);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_189, 14);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_189, 15);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_189, 16);
lean_inc_ref(x_210);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 lean_ctor_release(x_189, 5);
 lean_ctor_release(x_189, 6);
 lean_ctor_release(x_189, 7);
 lean_ctor_release(x_189, 8);
 lean_ctor_release(x_189, 9);
 lean_ctor_release(x_189, 10);
 lean_ctor_release(x_189, 11);
 lean_ctor_release(x_189, 12);
 lean_ctor_release(x_189, 13);
 lean_ctor_release(x_189, 14);
 lean_ctor_release(x_189, 15);
 lean_ctor_release(x_189, 16);
 x_211 = x_189;
} else {
 lean_dec_ref(x_189);
 x_211 = lean_box(0);
}
x_212 = 1;
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(0, 17, 1);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_194);
lean_ctor_set(x_213, 1, x_195);
lean_ctor_set(x_213, 2, x_196);
lean_ctor_set(x_213, 3, x_197);
lean_ctor_set(x_213, 4, x_198);
lean_ctor_set(x_213, 5, x_199);
lean_ctor_set(x_213, 6, x_200);
lean_ctor_set(x_213, 7, x_201);
lean_ctor_set(x_213, 8, x_202);
lean_ctor_set(x_213, 9, x_203);
lean_ctor_set(x_213, 10, x_204);
lean_ctor_set(x_213, 11, x_205);
lean_ctor_set(x_213, 12, x_206);
lean_ctor_set(x_213, 13, x_207);
lean_ctor_set(x_213, 14, x_208);
lean_ctor_set(x_213, 15, x_209);
lean_ctor_set(x_213, 16, x_210);
lean_ctor_set_uint8(x_213, sizeof(void*)*17, x_212);
if (lean_is_scalar(x_193)) {
 x_214 = lean_alloc_ctor(0, 4, 0);
} else {
 x_214 = x_193;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_190);
lean_ctor_set(x_214, 2, x_191);
lean_ctor_set(x_214, 3, x_192);
x_215 = lean_st_ref_set(x_5, x_214);
lean_dec(x_5);
x_216 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_217 = lean_alloc_ctor(0, 1, 0);
} else {
 x_217 = x_187;
}
lean_ctor_set(x_217, 0, x_216);
return x_217;
}
else
{
lean_dec(x_5);
return x_186;
}
}
else
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_4);
lean_dec(x_3);
x_219 = lean_ctor_get(x_2, 0);
lean_inc(x_219);
lean_dec_ref(x_2);
x_220 = l_Lean_Meta_Grind_getGoal___redArg(x_5);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec_ref(x_220);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec(x_221);
lean_inc(x_5);
x_223 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_222, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; 
lean_dec_ref(x_223);
x_224 = l_Lean_Meta_Grind_setGoal___redArg(x_219, x_5);
lean_dec(x_5);
return x_224;
}
else
{
lean_dec(x_219);
lean_dec(x_5);
return x_223;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_inc_ref(x_218);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_225 = lean_ctor_get(x_2, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_226 = x_2;
} else {
 lean_dec_ref(x_2);
 x_226 = lean_box(0);
}
x_227 = l_Lean_Meta_Grind_getGoal___redArg(x_5);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
x_230 = lean_st_ref_take(x_5);
x_231 = lean_ctor_get(x_230, 1);
lean_inc_ref(x_231);
x_232 = lean_ctor_get(x_230, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_230, 3);
lean_inc(x_233);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 lean_ctor_release(x_230, 2);
 lean_ctor_release(x_230, 3);
 x_234 = x_230;
} else {
 lean_dec_ref(x_230);
 x_234 = lean_box(0);
}
x_235 = l_Lean_Meta_Grind_mkChoice___closed__0;
x_236 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_236, 0, x_4);
lean_ctor_set(x_236, 1, x_228);
lean_ctor_set(x_236, 2, x_1);
lean_ctor_set(x_236, 3, x_218);
lean_ctor_set(x_236, 4, x_235);
lean_ctor_set(x_236, 5, x_3);
if (lean_is_scalar(x_226)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_226;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_233);
if (lean_is_scalar(x_234)) {
 x_238 = lean_alloc_ctor(0, 4, 0);
} else {
 x_238 = x_234;
}
lean_ctor_set(x_238, 0, x_225);
lean_ctor_set(x_238, 1, x_231);
lean_ctor_set(x_238, 2, x_232);
lean_ctor_set(x_238, 3, x_237);
x_239 = lean_st_ref_set(x_5, x_238);
lean_dec(x_5);
x_240 = lean_box(0);
if (lean_is_scalar(x_229)) {
 x_241 = lean_alloc_ctor(0, 1, 0);
} else {
 x_241 = x_229;
}
lean_ctor_set(x_241, 0, x_240);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_242 = l_Lean_Meta_Grind_mkChoice___closed__4;
x_243 = l_panic___at___Lean_Meta_Grind_mkChoice_spec__7(x_242, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_243;
}
}
}
else
{
uint8_t x_244; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_244 = !lean_is_exclusive(x_18);
if (x_244 == 0)
{
return x_18;
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_18, 0);
lean_inc(x_245);
lean_dec(x_18);
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_245);
return x_246;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1_spec__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_mkChoice_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_panic___at___Lean_Meta_Grind_mkChoice_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_mkChoice___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkChoice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_mkChoice(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Expr_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3_spec__3___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__6___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__6___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__6___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_Expr_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__3___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__6___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_22; lean_object* x_23; 
x_22 = lean_st_ref_get(x_3);
x_23 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0___redArg(x_22, x_2);
lean_dec_ref(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_inc_ref(x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_24 = lean_apply_7(x_1, x_2, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_37; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_37 = lean_unbox(x_27);
lean_dec(x_27);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_38 = lean_box(0);
lean_ctor_set(x_25, 0, x_38);
x_10 = x_25;
x_11 = x_38;
x_12 = lean_box(0);
goto block_17;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_25);
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_39);
lean_inc_ref(x_1);
x_41 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_39, x_3, x_28, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc_ref(x_40);
x_44 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_40, x_3, x_43, x_5, x_6, x_7, x_8);
x_18 = x_44;
goto block_21;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_18 = x_41;
goto block_21;
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_25);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_46);
lean_inc_ref(x_45);
x_29 = x_45;
x_30 = x_46;
x_31 = x_3;
goto block_36;
}
case 7:
{
lean_object* x_47; lean_object* x_48; 
lean_free_object(x_25);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_48);
lean_inc_ref(x_47);
x_29 = x_47;
x_30 = x_48;
x_31 = x_3;
goto block_36;
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_25);
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_ctor_get(x_2, 2);
x_51 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_49);
lean_inc_ref(x_1);
x_52 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_49, x_3, x_28, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_50);
lean_inc_ref(x_1);
x_55 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_50, x_3, x_54, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc_ref(x_51);
x_58 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_51, x_3, x_57, x_5, x_6, x_7, x_8);
x_18 = x_58;
goto block_21;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_18 = x_55;
goto block_21;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_18 = x_52;
goto block_21;
}
}
case 10:
{
lean_object* x_59; lean_object* x_60; 
lean_free_object(x_25);
x_59 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_59);
x_60 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_59, x_3, x_28, x_5, x_6, x_7, x_8);
x_18 = x_60;
goto block_21;
}
case 11:
{
lean_object* x_61; lean_object* x_62; 
lean_free_object(x_25);
x_61 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_61);
x_62 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_61, x_3, x_28, x_5, x_6, x_7, x_8);
x_18 = x_62;
goto block_21;
}
default: 
{
lean_object* x_63; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_63 = lean_box(0);
lean_ctor_set(x_25, 0, x_63);
x_10 = x_25;
x_11 = x_63;
x_12 = lean_box(0);
goto block_17;
}
}
}
block_36:
{
lean_object* x_32; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_32 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_29, x_31, x_28, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_30, x_31, x_34, x_5, x_6, x_7, x_8);
x_18 = x_35;
goto block_21;
}
else
{
lean_dec_ref(x_30);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_18 = x_32;
goto block_21;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_74; 
x_64 = lean_ctor_get(x_25, 0);
x_65 = lean_ctor_get(x_25, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_25);
x_74 = lean_unbox(x_64);
lean_dec(x_64);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_65);
x_10 = x_76;
x_11 = x_75;
x_12 = lean_box(0);
goto block_17;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_2, 0);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_77);
lean_inc_ref(x_1);
x_79 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_77, x_3, x_65, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
lean_inc_ref(x_78);
x_82 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_78, x_3, x_81, x_5, x_6, x_7, x_8);
x_18 = x_82;
goto block_21;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_18 = x_79;
goto block_21;
}
}
case 6:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_2, 1);
x_84 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_84);
lean_inc_ref(x_83);
x_66 = x_83;
x_67 = x_84;
x_68 = x_3;
goto block_73;
}
case 7:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_2, 1);
x_86 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_86);
lean_inc_ref(x_85);
x_66 = x_85;
x_67 = x_86;
x_68 = x_3;
goto block_73;
}
case 8:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_2, 1);
x_88 = lean_ctor_get(x_2, 2);
x_89 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_87);
lean_inc_ref(x_1);
x_90 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_87, x_3, x_65, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_88);
lean_inc_ref(x_1);
x_93 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_88, x_3, x_92, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
lean_inc_ref(x_89);
x_96 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_89, x_3, x_95, x_5, x_6, x_7, x_8);
x_18 = x_96;
goto block_21;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_18 = x_93;
goto block_21;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_18 = x_90;
goto block_21;
}
}
case 10:
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_97);
x_98 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_97, x_3, x_65, x_5, x_6, x_7, x_8);
x_18 = x_98;
goto block_21;
}
case 11:
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_99);
x_100 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_99, x_3, x_65, x_5, x_6, x_7, x_8);
x_18 = x_100;
goto block_21;
}
default: 
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_65);
x_10 = x_102;
x_11 = x_101;
x_12 = lean_box(0);
goto block_17;
}
}
}
block_73:
{
lean_object* x_69; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_69 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_66, x_68, x_65, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_67, x_68, x_71, x_5, x_6, x_7, x_8);
x_18 = x_72;
goto block_21;
}
else
{
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_18 = x_69;
goto block_21;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_103 = !lean_is_exclusive(x_24);
if (x_103 == 0)
{
return x_24;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_24, 0);
lean_inc(x_104);
lean_dec(x_24);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_106 = !lean_is_exclusive(x_23);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_23, 0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_4);
lean_ctor_set_tag(x_23, 0);
lean_ctor_set(x_23, 0, x_108);
return x_23;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_23, 0);
lean_inc(x_109);
lean_dec(x_23);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_4);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
block_17:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_st_ref_take(x_3);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2___redArg(x_13, x_2, x_11);
x_15 = lean_st_ref_set(x_3, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_10);
return x_16;
}
block_21:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_10 = x_19;
x_11 = x_20;
x_12 = lean_box(0);
goto block_17;
}
else
{
lean_dec_ref(x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasFVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = l_Lean_FVarId_getDecl___redArg(x_12, x_3, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_15 = x_13;
} else {
 lean_dec_ref(x_13);
 x_15 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_LocalDecl_index(x_14);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_16 = x_23;
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = l_Lean_LocalDecl_index(x_14);
lean_dec(x_14);
x_26 = lean_nat_dec_le(x_24, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
x_16 = x_2;
goto block_21;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
lean_ctor_set(x_2, 0, x_25);
x_16 = x_2;
goto block_21;
}
else
{
lean_object* x_29; 
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_25);
x_16 = x_29;
goto block_21;
}
}
}
block_21:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_15)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_15;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_33 = lean_box(x_8);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_2);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__4;
x_8 = lean_st_mk_ref(x_7);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lam__0___boxed), 7, 0);
x_10 = lean_box(0);
x_11 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_9, x_1, x_8, x_10, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_8);
lean_dec(x_8);
lean_dec_ref(x_15);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_8);
lean_dec(x_8);
lean_dec_ref(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0_spec__2_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExpr_visit___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 3);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 3, x_6);
x_7 = lean_st_ref_set(x_1, x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
x_15 = lean_st_ref_set(x_1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_st_ref_get(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = lean_st_mk_ref(x_13);
x_15 = l_Lean_MVarId_assignFalseProof(x_1, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_st_ref_get(x_2);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_List_isEmpty___redArg(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_List_getLast___redArg(x_12);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lam__0___boxed), 11, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_1);
lean_inc(x_2);
x_21 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_take(x_2);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_23);
x_27 = lean_st_ref_set(x_2, x_24);
x_28 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_2);
lean_dec(x_2);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_24, 1);
x_30 = lean_ctor_get(x_24, 2);
x_31 = lean_ctor_get(x_24, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_2, x_32);
x_34 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_2);
lean_dec(x_2);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
lean_ctor_set(x_2, 0, x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec_ref(x_13);
x_21 = lean_ctor_get(x_17, 2);
lean_inc_ref(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_22, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_dec_ref(x_23);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_20);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_20);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_13, 1);
x_30 = lean_ctor_get(x_17, 5);
x_31 = lean_ctor_get(x_17, 3);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
x_35 = lean_st_ref_take(x_3);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_35, 3);
lean_dec(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
lean_inc(x_30);
lean_ctor_set(x_17, 3, x_34);
lean_inc(x_29);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_35, 3, x_18);
lean_ctor_set(x_35, 0, x_33);
x_39 = lean_st_ref_set(x_3, x_35);
lean_dec(x_3);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_30);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_2, 0, x_41);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_2);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_35, 1);
x_44 = lean_ctor_get(x_35, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
lean_inc(x_30);
lean_ctor_set(x_17, 3, x_34);
lean_inc(x_29);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_17);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_18);
x_46 = lean_st_ref_set(x_3, x_45);
lean_dec(x_3);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_30);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_2, 0, x_48);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_2);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_st_ref_take(x_3);
x_53 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_52, 2);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
lean_inc(x_30);
lean_ctor_set(x_17, 3, x_51);
lean_inc(x_29);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_17);
lean_ctor_set(x_56, 1, x_29);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 4, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_54);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_st_ref_set(x_3, x_57);
lean_dec(x_3);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_30);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_2, 0, x_60);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_2);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_62 = lean_ctor_get(x_13, 1);
x_63 = lean_ctor_get(x_17, 0);
x_64 = lean_ctor_get(x_17, 1);
x_65 = lean_ctor_get(x_17, 2);
x_66 = lean_ctor_get(x_17, 4);
x_67 = lean_ctor_get(x_17, 5);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_17);
x_68 = lean_ctor_get(x_18, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_70 = x_18;
} else {
 lean_dec_ref(x_18);
 x_70 = lean_box(0);
}
x_71 = lean_st_ref_take(x_3);
x_72 = lean_ctor_get(x_71, 1);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_71, 2);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
lean_inc(x_67);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_63);
lean_ctor_set(x_75, 1, x_64);
lean_ctor_set(x_75, 2, x_65);
lean_ctor_set(x_75, 3, x_69);
lean_ctor_set(x_75, 4, x_66);
lean_ctor_set(x_75, 5, x_67);
lean_inc(x_62);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_62);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 4, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_72);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_76);
x_78 = lean_st_ref_set(x_3, x_77);
lean_dec(x_3);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_67);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_2, 0, x_80);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_2);
return x_81;
}
}
}
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
lean_dec(x_2);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_83 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 3);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_86, 1);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec_ref(x_82);
x_90 = lean_ctor_get(x_86, 2);
lean_inc_ref(x_90);
lean_dec(x_86);
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
lean_dec_ref(x_88);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_92 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_91, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_dec_ref(x_92);
lean_inc(x_1);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_89);
x_2 = x_93;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_89);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_96 = x_92;
} else {
 lean_dec_ref(x_92);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_98 = lean_ctor_get(x_82, 1);
x_99 = lean_ctor_get(x_86, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_86, 1);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_86, 2);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_86, 4);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_86, 5);
lean_inc(x_103);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 x_104 = x_86;
} else {
 lean_dec_ref(x_86);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_87, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_87, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_107 = x_87;
} else {
 lean_dec_ref(x_87);
 x_107 = lean_box(0);
}
x_108 = lean_st_ref_take(x_3);
x_109 = lean_ctor_get(x_108, 1);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_108, 2);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
lean_inc(x_103);
if (lean_is_scalar(x_104)) {
 x_112 = lean_alloc_ctor(0, 6, 0);
} else {
 x_112 = x_104;
}
lean_ctor_set(x_112, 0, x_99);
lean_ctor_set(x_112, 1, x_100);
lean_ctor_set(x_112, 2, x_101);
lean_ctor_set(x_112, 3, x_106);
lean_ctor_set(x_112, 4, x_102);
lean_ctor_set(x_112, 5, x_103);
lean_inc(x_98);
if (lean_is_scalar(x_107)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_107;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_98);
if (lean_is_scalar(x_111)) {
 x_114 = lean_alloc_ctor(0, 4, 0);
} else {
 x_114 = x_111;
}
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_113);
x_115 = lean_st_ref_set(x_3, x_114);
lean_dec(x_3);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_103);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_82);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 4);
x_20 = lean_ctor_get(x_13, 1);
lean_dec(x_20);
x_21 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_22 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_16);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_17);
lean_ctor_set(x_13, 4, x_26);
lean_ctor_set(x_13, 3, x_27);
lean_ctor_set(x_13, 2, x_28);
lean_ctor_set(x_13, 1, x_21);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_11, 1, x_22);
x_29 = l_ReaderT_instMonad___redArg(x_11);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_38 = lean_ctor_get(x_31, 1);
lean_dec(x_38);
x_39 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_40 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_36);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_35);
lean_ctor_set(x_31, 4, x_44);
lean_ctor_set(x_31, 3, x_45);
lean_ctor_set(x_31, 2, x_46);
lean_ctor_set(x_31, 1, x_39);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_29, 1, x_40);
x_47 = l_ReaderT_instMonad___redArg(x_29);
x_48 = l_ReaderT_instMonad___redArg(x_47);
x_49 = l_ReaderT_instMonad___redArg(x_48);
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = lean_box(0);
x_52 = l_instInhabitedOfMonad___redArg(x_50, x_51);
x_53 = lean_panic_fn(x_52, x_1);
x_54 = lean_apply_9(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_55 = lean_ctor_get(x_31, 0);
x_56 = lean_ctor_get(x_31, 2);
x_57 = lean_ctor_get(x_31, 3);
x_58 = lean_ctor_get(x_31, 4);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_31);
x_59 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_60 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_55);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_61, 0, x_55);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_62, 0, x_55);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_64, 0, x_58);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_65, 0, x_57);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_66, 0, x_56);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_65);
lean_ctor_set(x_67, 4, x_64);
lean_ctor_set(x_29, 1, x_60);
lean_ctor_set(x_29, 0, x_67);
x_68 = l_ReaderT_instMonad___redArg(x_29);
x_69 = l_ReaderT_instMonad___redArg(x_68);
x_70 = l_ReaderT_instMonad___redArg(x_69);
x_71 = l_ReaderT_instMonad___redArg(x_70);
x_72 = lean_box(0);
x_73 = l_instInhabitedOfMonad___redArg(x_71, x_72);
x_74 = lean_panic_fn(x_73, x_1);
x_75 = lean_apply_9(x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_76 = lean_ctor_get(x_29, 0);
lean_inc(x_76);
lean_dec(x_29);
x_77 = lean_ctor_get(x_76, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_76, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 4);
lean_inc(x_80);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 lean_ctor_release(x_76, 3);
 lean_ctor_release(x_76, 4);
 x_81 = x_76;
} else {
 lean_dec_ref(x_76);
 x_81 = lean_box(0);
}
x_82 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_83 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_77);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_84, 0, x_77);
x_85 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_85, 0, x_77);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_87, 0, x_80);
x_88 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_88, 0, x_79);
x_89 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_89, 0, x_78);
if (lean_is_scalar(x_81)) {
 x_90 = lean_alloc_ctor(0, 5, 0);
} else {
 x_90 = x_81;
}
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_82);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_88);
lean_ctor_set(x_90, 4, x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
x_92 = l_ReaderT_instMonad___redArg(x_91);
x_93 = l_ReaderT_instMonad___redArg(x_92);
x_94 = l_ReaderT_instMonad___redArg(x_93);
x_95 = l_ReaderT_instMonad___redArg(x_94);
x_96 = lean_box(0);
x_97 = l_instInhabitedOfMonad___redArg(x_95, x_96);
x_98 = lean_panic_fn(x_97, x_1);
x_99 = lean_apply_9(x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_100 = lean_ctor_get(x_13, 0);
x_101 = lean_ctor_get(x_13, 2);
x_102 = lean_ctor_get(x_13, 3);
x_103 = lean_ctor_get(x_13, 4);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_13);
x_104 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_105 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_100);
x_106 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_106, 0, x_100);
x_107 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_107, 0, x_100);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_109, 0, x_103);
x_110 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_110, 0, x_102);
x_111 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_111, 0, x_101);
x_112 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_104);
lean_ctor_set(x_112, 2, x_111);
lean_ctor_set(x_112, 3, x_110);
lean_ctor_set(x_112, 4, x_109);
lean_ctor_set(x_11, 1, x_105);
lean_ctor_set(x_11, 0, x_112);
x_113 = l_ReaderT_instMonad___redArg(x_11);
x_114 = lean_ctor_get(x_113, 0);
lean_inc_ref(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_114, 0);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_114, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 4);
lean_inc(x_119);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_120 = x_114;
} else {
 lean_dec_ref(x_114);
 x_120 = lean_box(0);
}
x_121 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_122 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_116);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_123, 0, x_116);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_124, 0, x_116);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_126, 0, x_119);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_127, 0, x_118);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_128, 0, x_117);
if (lean_is_scalar(x_120)) {
 x_129 = lean_alloc_ctor(0, 5, 0);
} else {
 x_129 = x_120;
}
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_121);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_127);
lean_ctor_set(x_129, 4, x_126);
if (lean_is_scalar(x_115)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_115;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_122);
x_131 = l_ReaderT_instMonad___redArg(x_130);
x_132 = l_ReaderT_instMonad___redArg(x_131);
x_133 = l_ReaderT_instMonad___redArg(x_132);
x_134 = l_ReaderT_instMonad___redArg(x_133);
x_135 = lean_box(0);
x_136 = l_instInhabitedOfMonad___redArg(x_134, x_135);
x_137 = lean_panic_fn(x_136, x_1);
x_138 = lean_apply_9(x_137, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_139 = lean_ctor_get(x_11, 0);
lean_inc(x_139);
lean_dec(x_11);
x_140 = lean_ctor_get(x_139, 0);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_139, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 4);
lean_inc(x_143);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 lean_ctor_release(x_139, 2);
 lean_ctor_release(x_139, 3);
 lean_ctor_release(x_139, 4);
 x_144 = x_139;
} else {
 lean_dec_ref(x_139);
 x_144 = lean_box(0);
}
x_145 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2;
x_146 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3;
lean_inc_ref(x_140);
x_147 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_147, 0, x_140);
x_148 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_148, 0, x_140);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_150, 0, x_143);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_151, 0, x_142);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_152, 0, x_141);
if (lean_is_scalar(x_144)) {
 x_153 = lean_alloc_ctor(0, 5, 0);
} else {
 x_153 = x_144;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_145);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_153, 3, x_151);
lean_ctor_set(x_153, 4, x_150);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_146);
x_155 = l_ReaderT_instMonad___redArg(x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_158);
x_159 = lean_ctor_get(x_156, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_156, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_156, 4);
lean_inc(x_161);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 lean_ctor_release(x_156, 2);
 lean_ctor_release(x_156, 3);
 lean_ctor_release(x_156, 4);
 x_162 = x_156;
} else {
 lean_dec_ref(x_156);
 x_162 = lean_box(0);
}
x_163 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4;
x_164 = l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5;
lean_inc_ref(x_158);
x_165 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_165, 0, x_158);
x_166 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_166, 0, x_158);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_168, 0, x_161);
x_169 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_169, 0, x_160);
x_170 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_170, 0, x_159);
if (lean_is_scalar(x_162)) {
 x_171 = lean_alloc_ctor(0, 5, 0);
} else {
 x_171 = x_162;
}
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_163);
lean_ctor_set(x_171, 2, x_170);
lean_ctor_set(x_171, 3, x_169);
lean_ctor_set(x_171, 4, x_168);
if (lean_is_scalar(x_157)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_157;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_164);
x_173 = l_ReaderT_instMonad___redArg(x_172);
x_174 = l_ReaderT_instMonad___redArg(x_173);
x_175 = l_ReaderT_instMonad___redArg(x_174);
x_176 = l_ReaderT_instMonad___redArg(x_175);
x_177 = lean_box(0);
x_178 = l_instInhabitedOfMonad___redArg(x_176, x_177);
x_179 = lean_panic_fn(x_178, x_1);
x_180 = lean_apply_9(x_179, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_180;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.SearchM.0.Lean.Meta.Grind.nextChronoGoal\?", 73, 73);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(162u);
x_4 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__0;
x_5 = l_Lean_Meta_Grind_mkChoice___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_st_ref_get(x_1);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0(x_12, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_14);
x_18 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__2;
x_19 = l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec_ref(x_17);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__2;
x_24 = l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1(x_23, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_Expr_isFalse(x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elim", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesOn", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0___redArg(x_1, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_13 = x_11;
} else {
 lean_dec_ref(x_11);
 x_13 = lean_box(0);
}
x_18 = lean_unbox(x_12);
lean_dec(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__2;
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Expr_isAppOfArity(x_10, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__4;
x_23 = l_Lean_Expr_isAppOfArity(x_10, x_22, x_20);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_10);
x_24 = lean_box(0);
lean_ctor_set(x_8, 0, x_24);
return x_8;
}
else
{
lean_free_object(x_8);
goto block_17;
}
}
else
{
lean_free_object(x_8);
goto block_17;
}
}
else
{
lean_object* x_25; 
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
if (lean_is_scalar(x_13)) {
 x_16 = lean_alloc_ctor(0, 1, 0);
} else {
 x_16 = x_13;
}
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_8);
lean_dec(x_10);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_37 = lean_unbox(x_31);
lean_dec(x_31);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__2;
x_39 = lean_unsigned_to_nat(2u);
x_40 = l_Lean_Expr_isAppOfArity(x_29, x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__4;
x_42 = l_Lean_Expr_isAppOfArity(x_29, x_41, x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_32);
lean_dec(x_29);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
goto block_36;
}
}
else
{
goto block_36;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_29);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_Expr_appArg_x21(x_29);
lean_dec(x_29);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_29);
x_47 = lean_ctor_get(x_30, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_48 = x_30;
} else {
 lean_dec_ref(x_30);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = l_Lean_mkMVar(x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1___redArg(x_1, x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = lean_st_mk_ref(x_11);
x_13 = lean_st_ref_get(x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = lean_st_ref_get(x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_st_ref_get(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_st_mk_ref(x_12);
x_14 = lean_st_ref_take(x_7);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_1);
x_17 = lean_st_ref_set(x_7, x_14);
x_18 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_14, 1);
x_23 = lean_ctor_get(x_14, 2);
x_24 = lean_ctor_get(x_14, 3);
x_25 = lean_ctor_get(x_14, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
lean_ctor_set(x_26, 4, x_25);
x_27 = lean_st_ref_set(x_7, x_26);
x_28 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__0___boxed), 9, 0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_20);
x_24 = lean_st_ref_set(x_2, x_21);
x_25 = l_Lean_instantiateMVarsCore(x_19, x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__1___boxed), 10, 1);
lean_closure_set(x_31, 0, x_27);
lean_inc(x_2);
x_32 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_30, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_2);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_35);
x_39 = lean_st_ref_set(x_2, x_36);
lean_dec(x_2);
lean_ctor_set(x_32, 0, x_26);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_ctor_get(x_36, 2);
x_42 = lean_ctor_get(x_36, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_st_ref_set(x_2, x_43);
lean_dec(x_2);
lean_ctor_set(x_32, 0, x_26);
return x_32;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_take(x_2);
x_48 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 3);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 4, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
lean_ctor_set(x_52, 3, x_50);
x_53 = lean_st_ref_set(x_2, x_52);
lean_dec(x_2);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_26);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_26);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
return x_32;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
lean_dec(x_32);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_ctor_get(x_21, 1);
x_59 = lean_ctor_get(x_21, 2);
x_60 = lean_ctor_get(x_21, 3);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_21);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_20);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_st_ref_set(x_2, x_61);
x_63 = l_Lean_instantiateMVarsCore(x_19, x_1);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__1___boxed), 10, 1);
lean_closure_set(x_69, 0, x_65);
lean_inc(x_2);
x_70 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_68, x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_st_ref_take(x_2);
x_75 = lean_ctor_get(x_74, 1);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_74, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 3);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 4, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_77);
x_80 = lean_st_ref_set(x_2, x_79);
lean_dec(x_2);
if (lean_is_scalar(x_72)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_72;
}
lean_ctor_set(x_81, 0, x_64);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_64);
lean_dec(x_2);
x_82 = lean_ctor_get(x_70, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_83 = x_70;
} else {
 lean_dec_ref(x_70);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_85 = !lean_is_exclusive(x_17);
if (x_85 == 0)
{
return x_17;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_17, 0);
lean_inc(x_86);
lean_dec(x_17);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_st_ref_get(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_st_mk_ref(x_12);
x_14 = l_Lean_MVarId_getDecl(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_st_ref_get(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_st_mk_ref(x_12);
x_14 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_isTargetFalse(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_st_ref_get(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_st_mk_ref(x_12);
x_14 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_2);
x_14 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
x_22 = lean_st_ref_set(x_2, x_19);
lean_dec(x_2);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 2);
x_25 = lean_ctor_get(x_19, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_st_ref_set(x_2, x_26);
lean_dec(x_2);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_take(x_2);
x_32 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_31, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 3);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 4, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
x_37 = lean_st_ref_set(x_2, x_36);
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_29);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_st_ref_get(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = lean_st_mk_ref(x_13);
x_15 = l_Lean_MVarId_assignFalseProof(x_1, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_3);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
lean_ctor_set(x_2, 0, x_22);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_23 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
lean_ctor_set(x_2, 0, x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_2);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_3);
lean_dec(x_3);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_28 = x_27;
} else {
 lean_dec_ref(x_27);
 x_28 = lean_box(0);
}
x_29 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_13, 1, x_30);
lean_ctor_set(x_2, 0, x_29);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_2);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_13, 1);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_16, 1);
x_38 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_39 = lean_ctor_get(x_36, 1);
lean_inc_ref(x_39);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 2);
x_45 = lean_ctor_get(x_36, 3);
x_46 = lean_ctor_get(x_36, 4);
x_47 = lean_ctor_get(x_36, 5);
x_48 = lean_ctor_get(x_36, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
lean_inc(x_49);
x_51 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_51, 0, x_49);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_52 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_50, x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_take(x_3);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_56);
x_60 = lean_st_ref_set(x_3, x_57);
x_61 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_61);
lean_dec(x_55);
x_62 = lean_local_ctx_num_indices(x_61);
x_63 = lean_nat_dec_lt(x_35, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_64; 
lean_free_object(x_52);
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_64 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_65);
lean_inc(x_49);
x_66 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_49, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
lean_dec_ref(x_66);
x_67 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
lean_inc(x_49);
x_71 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_71, 0, x_49);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_72 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_70, x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_take(x_3);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_75);
x_79 = lean_st_ref_set(x_3, x_76);
x_80 = lean_unbox(x_74);
lean_dec(x_74);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
lean_dec(x_65);
lean_dec(x_49);
lean_dec(x_1);
x_81 = lean_st_ref_take(x_3);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 3);
lean_dec(x_83);
lean_inc(x_37);
lean_ctor_set(x_81, 3, x_37);
x_84 = lean_st_ref_set(x_3, x_81);
x_85 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_87);
lean_ctor_set(x_2, 0, x_67);
lean_ctor_set(x_85, 0, x_2);
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec(x_85);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_88);
lean_ctor_set(x_2, 0, x_67);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_2);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_free_object(x_67);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_90 = !lean_is_exclusive(x_85);
if (x_90 == 0)
{
return x_85;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_81, 0);
x_94 = lean_ctor_get(x_81, 1);
x_95 = lean_ctor_get(x_81, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_81);
lean_inc(x_37);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_37);
x_97 = lean_st_ref_set(x_3, x_96);
x_98 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_99);
lean_ctor_set(x_2, 0, x_67);
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_2);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_67);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_102 = lean_ctor_get(x_98, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_103 = x_98;
} else {
 lean_dec_ref(x_98);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_34);
lean_inc(x_65);
x_105 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_105, 0, x_65);
x_106 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_106, 0, x_105);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_107 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_49, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
lean_dec(x_1);
lean_inc(x_65);
x_109 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_109, 0);
lean_dec(x_111);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_108);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_2, 0, x_67);
lean_ctor_set(x_109, 0, x_2);
return x_109;
}
else
{
lean_object* x_112; 
lean_dec(x_109);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_108);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_2, 0, x_67);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_2);
return x_112;
}
}
else
{
uint8_t x_113; 
lean_free_object(x_67);
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_113 = !lean_is_exclusive(x_109);
if (x_113 == 0)
{
return x_109;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; 
lean_free_object(x_67);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_116 = lean_ctor_get(x_108, 0);
lean_inc(x_116);
lean_dec_ref(x_108);
lean_ctor_set(x_32, 1, x_116);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
}
else
{
uint8_t x_118; 
lean_free_object(x_67);
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_107);
if (x_118 == 0)
{
return x_107;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_107, 0);
lean_inc(x_119);
lean_dec(x_107);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_76, 1);
x_122 = lean_ctor_get(x_76, 2);
x_123 = lean_ctor_get(x_76, 3);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_76);
x_124 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_124, 0, x_75);
lean_ctor_set(x_124, 1, x_121);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_123);
x_125 = lean_st_ref_set(x_3, x_124);
x_126 = lean_unbox(x_74);
lean_dec(x_74);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_65);
lean_dec(x_49);
lean_dec(x_1);
x_127 = lean_st_ref_take(x_3);
x_128 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_127, 2);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 4, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_37);
x_133 = lean_st_ref_set(x_3, x_132);
x_134 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_135);
lean_ctor_set(x_2, 0, x_67);
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 1, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_2);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_free_object(x_67);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_138 = lean_ctor_get(x_134, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_139 = x_134;
} else {
 lean_dec_ref(x_134);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_34);
lean_inc(x_65);
x_141 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_141, 0, x_65);
x_142 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_142, 0, x_141);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_143 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_49, x_142, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_dec(x_1);
lean_inc(x_65);
x_145 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_146 = x_145;
} else {
 lean_dec_ref(x_145);
 x_146 = lean_box(0);
}
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_144);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_2, 0, x_67);
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 1, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_2);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_free_object(x_67);
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_149 = x_145;
} else {
 lean_dec_ref(x_145);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
}
else
{
lean_object* x_151; 
lean_free_object(x_67);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_151 = lean_ctor_get(x_144, 0);
lean_inc(x_151);
lean_dec_ref(x_144);
lean_ctor_set(x_32, 1, x_151);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_free_object(x_67);
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = lean_ctor_get(x_143, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_154 = x_143;
} else {
 lean_dec_ref(x_143);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
}
}
else
{
uint8_t x_156; 
lean_free_object(x_67);
lean_dec(x_65);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_72);
if (x_156 == 0)
{
return x_72;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_72, 0);
lean_inc(x_157);
lean_dec(x_72);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_67, 0);
lean_inc(x_159);
lean_dec(x_67);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
lean_inc(x_49);
x_161 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_161, 0, x_49);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_162 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_160, x_161, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_st_ref_take(x_3);
x_167 = lean_ctor_get(x_166, 1);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_166, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 x_170 = x_166;
} else {
 lean_dec_ref(x_166);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 4, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_169);
x_172 = lean_st_ref_set(x_3, x_171);
x_173 = lean_unbox(x_164);
lean_dec(x_164);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_65);
lean_dec(x_49);
lean_dec(x_1);
x_174 = lean_st_ref_take(x_3);
x_175 = lean_ctor_get(x_174, 0);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_174, 2);
lean_inc(x_177);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 lean_ctor_release(x_174, 2);
 lean_ctor_release(x_174, 3);
 x_178 = x_174;
} else {
 lean_dec_ref(x_174);
 x_178 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 4, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_37);
x_180 = lean_st_ref_set(x_3, x_179);
x_181 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_2, 0, x_184);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 1, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_2);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_186 = lean_ctor_get(x_181, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_187 = x_181;
} else {
 lean_dec_ref(x_181);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_34);
lean_inc(x_65);
x_189 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_189, 0, x_65);
x_190 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_190, 0, x_189);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_191 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_49, x_190, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
lean_dec(x_1);
lean_inc(x_65);
x_193 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_194 = x_193;
} else {
 lean_dec_ref(x_193);
 x_194 = lean_box(0);
}
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_2, 0, x_195);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 1, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_2);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_197 = lean_ctor_get(x_193, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_198 = x_193;
} else {
 lean_dec_ref(x_193);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 1, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_197);
return x_199;
}
}
else
{
lean_object* x_200; 
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_200 = lean_ctor_get(x_192, 0);
lean_inc(x_200);
lean_dec_ref(x_192);
lean_ctor_set(x_32, 1, x_200);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_202 = lean_ctor_get(x_191, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_203 = x_191;
} else {
 lean_dec_ref(x_191);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_65);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_205 = lean_ctor_get(x_162, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_206 = x_162;
} else {
 lean_dec_ref(x_162);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_65);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_66);
if (x_208 == 0)
{
return x_66;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_66, 0);
lean_inc(x_209);
lean_dec(x_66);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_64);
if (x_211 == 0)
{
return x_64;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_64, 0);
lean_inc(x_212);
lean_dec(x_64);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_45);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_215 = lean_ctor_get(x_45, 0);
x_216 = lean_ctor_get(x_45, 1);
x_217 = lean_st_ref_take(x_3);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_217, 3);
lean_dec(x_219);
x_220 = lean_ctor_get(x_217, 0);
lean_dec(x_220);
lean_inc(x_47);
lean_ctor_set(x_36, 3, x_216);
lean_inc(x_37);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_217, 3, x_45);
lean_ctor_set(x_217, 0, x_215);
x_221 = lean_st_ref_set(x_3, x_217);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_38);
lean_ctor_set(x_2, 0, x_222);
lean_ctor_set(x_52, 0, x_2);
return x_52;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_217, 1);
x_224 = lean_ctor_get(x_217, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_217);
lean_inc(x_47);
lean_ctor_set(x_36, 3, x_216);
lean_inc(x_37);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 0, x_36);
x_225 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_225, 0, x_215);
lean_ctor_set(x_225, 1, x_223);
lean_ctor_set(x_225, 2, x_224);
lean_ctor_set(x_225, 3, x_45);
x_226 = lean_st_ref_set(x_3, x_225);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_38);
lean_ctor_set(x_2, 0, x_227);
lean_ctor_set(x_52, 0, x_2);
return x_52;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_228 = lean_ctor_get(x_45, 0);
x_229 = lean_ctor_get(x_45, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_45);
x_230 = lean_st_ref_take(x_3);
x_231 = lean_ctor_get(x_230, 1);
lean_inc_ref(x_231);
x_232 = lean_ctor_get(x_230, 2);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 lean_ctor_release(x_230, 2);
 lean_ctor_release(x_230, 3);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
lean_inc(x_47);
lean_ctor_set(x_36, 3, x_229);
lean_inc(x_37);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_36);
lean_ctor_set(x_234, 1, x_37);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(0, 4, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_228);
lean_ctor_set(x_235, 1, x_231);
lean_ctor_set(x_235, 2, x_232);
lean_ctor_set(x_235, 3, x_234);
x_236 = lean_st_ref_set(x_3, x_235);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_38);
lean_ctor_set(x_2, 0, x_237);
lean_ctor_set(x_52, 0, x_2);
return x_52;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_free_object(x_52);
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_37);
lean_dec_ref(x_16);
x_238 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec(x_239);
lean_inc(x_34);
x_241 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_241, 0, x_49);
lean_closure_set(x_241, 1, x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_242 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_240, x_241, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
lean_dec_ref(x_242);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_st_ref_take(x_3);
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_245, 0);
lean_dec(x_247);
lean_ctor_set(x_245, 0, x_244);
x_248 = lean_st_ref_set(x_3, x_245);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_245, 1);
x_251 = lean_ctor_get(x_245, 2);
x_252 = lean_ctor_get(x_245, 3);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_245);
x_253 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_253, 0, x_244);
lean_ctor_set(x_253, 1, x_250);
lean_ctor_set(x_253, 2, x_251);
lean_ctor_set(x_253, 3, x_252);
x_254 = lean_st_ref_set(x_3, x_253);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
}
else
{
uint8_t x_256; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_242);
if (x_256 == 0)
{
return x_242;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_242, 0);
lean_inc(x_257);
lean_dec(x_242);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_259 = lean_ctor_get(x_57, 1);
x_260 = lean_ctor_get(x_57, 2);
x_261 = lean_ctor_get(x_57, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_57);
x_262 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_262, 0, x_56);
lean_ctor_set(x_262, 1, x_259);
lean_ctor_set(x_262, 2, x_260);
lean_ctor_set(x_262, 3, x_261);
x_263 = lean_st_ref_set(x_3, x_262);
x_264 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_264);
lean_dec(x_55);
x_265 = lean_local_ctx_num_indices(x_264);
x_266 = lean_nat_dec_lt(x_35, x_265);
lean_dec(x_265);
if (x_266 == 0)
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_267; 
lean_free_object(x_52);
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_267 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec_ref(x_267);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_268);
lean_inc(x_49);
x_269 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_49, x_268, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec_ref(x_269);
x_270 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
lean_dec(x_271);
lean_inc(x_49);
x_274 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_274, 0, x_49);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_275 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_273, x_274, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_st_ref_take(x_3);
x_280 = lean_ctor_get(x_279, 1);
lean_inc_ref(x_280);
x_281 = lean_ctor_get(x_279, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_279, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 x_283 = x_279;
} else {
 lean_dec_ref(x_279);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 4, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_278);
lean_ctor_set(x_284, 1, x_280);
lean_ctor_set(x_284, 2, x_281);
lean_ctor_set(x_284, 3, x_282);
x_285 = lean_st_ref_set(x_3, x_284);
x_286 = lean_unbox(x_277);
lean_dec(x_277);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_268);
lean_dec(x_49);
lean_dec(x_1);
x_287 = lean_st_ref_take(x_3);
x_288 = lean_ctor_get(x_287, 0);
lean_inc_ref(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc_ref(x_289);
x_290 = lean_ctor_get(x_287, 2);
lean_inc(x_290);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_291 = x_287;
} else {
 lean_dec_ref(x_287);
 x_291 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 4, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_289);
lean_ctor_set(x_292, 2, x_290);
lean_ctor_set(x_292, 3, x_37);
x_293 = lean_st_ref_set(x_3, x_292);
x_294 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_296 = x_294;
} else {
 lean_dec_ref(x_294);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_272;
 lean_ctor_set_tag(x_297, 1);
}
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_2, 0, x_297);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(0, 1, 0);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_2);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_272);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_299 = lean_ctor_get(x_294, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_300 = x_294;
} else {
 lean_dec_ref(x_294);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_34);
lean_inc(x_268);
x_302 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_302, 0, x_268);
x_303 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_303, 0, x_302);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_304 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_49, x_303, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec_ref(x_304);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; 
lean_dec(x_1);
lean_inc(x_268);
x_306 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_268, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_307 = x_306;
} else {
 lean_dec_ref(x_306);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_308 = lean_alloc_ctor(1, 1, 0);
} else {
 x_308 = x_272;
 lean_ctor_set_tag(x_308, 1);
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_32, 0, x_268);
lean_ctor_set(x_2, 0, x_308);
if (lean_is_scalar(x_307)) {
 x_309 = lean_alloc_ctor(0, 1, 0);
} else {
 x_309 = x_307;
}
lean_ctor_set(x_309, 0, x_2);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_272);
lean_dec(x_268);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_310 = lean_ctor_get(x_306, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_311 = x_306;
} else {
 lean_dec_ref(x_306);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 1, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_310);
return x_312;
}
}
else
{
lean_object* x_313; 
lean_dec(x_272);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_313 = lean_ctor_get(x_305, 0);
lean_inc(x_313);
lean_dec_ref(x_305);
lean_ctor_set(x_32, 1, x_313);
lean_ctor_set(x_32, 0, x_268);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_272);
lean_dec(x_268);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_315 = lean_ctor_get(x_304, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 x_316 = x_304;
} else {
 lean_dec_ref(x_304);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 1, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_315);
return x_317;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_272);
lean_dec(x_268);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_318 = lean_ctor_get(x_275, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_319 = x_275;
} else {
 lean_dec_ref(x_275);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 1, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_318);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_268);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_321 = lean_ctor_get(x_269, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_322 = x_269;
} else {
 lean_dec_ref(x_269);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_321);
return x_323;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_324 = lean_ctor_get(x_267, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_325 = x_267;
} else {
 lean_dec_ref(x_267);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 1, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_324);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_327 = lean_ctor_get(x_45, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_45, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_329 = x_45;
} else {
 lean_dec_ref(x_45);
 x_329 = lean_box(0);
}
x_330 = lean_st_ref_take(x_3);
x_331 = lean_ctor_get(x_330, 1);
lean_inc_ref(x_331);
x_332 = lean_ctor_get(x_330, 2);
lean_inc(x_332);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 x_333 = x_330;
} else {
 lean_dec_ref(x_330);
 x_333 = lean_box(0);
}
lean_inc(x_47);
lean_ctor_set(x_36, 3, x_328);
lean_inc(x_37);
if (lean_is_scalar(x_329)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_329;
}
lean_ctor_set(x_334, 0, x_36);
lean_ctor_set(x_334, 1, x_37);
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 4, 0);
} else {
 x_335 = x_333;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_331);
lean_ctor_set(x_335, 2, x_332);
lean_ctor_set(x_335, 3, x_334);
x_336 = lean_st_ref_set(x_3, x_335);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
x_337 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_337, 0, x_38);
lean_ctor_set(x_2, 0, x_337);
lean_ctor_set(x_52, 0, x_2);
return x_52;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_free_object(x_52);
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_37);
lean_dec_ref(x_16);
x_338 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec(x_339);
lean_inc(x_34);
x_341 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_341, 0, x_49);
lean_closure_set(x_341, 1, x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_342 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_340, x_341, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec_ref(x_342);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
lean_dec(x_343);
x_345 = lean_st_ref_take(x_3);
x_346 = lean_ctor_get(x_345, 1);
lean_inc_ref(x_346);
x_347 = lean_ctor_get(x_345, 2);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 3);
lean_inc(x_348);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 x_349 = x_345;
} else {
 lean_dec_ref(x_345);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(0, 4, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_344);
lean_ctor_set(x_350, 1, x_346);
lean_ctor_set(x_350, 2, x_347);
lean_ctor_set(x_350, 3, x_348);
x_351 = lean_st_ref_set(x_3, x_350);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_353 = lean_ctor_get(x_342, 0);
lean_inc(x_353);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_354 = x_342;
} else {
 lean_dec_ref(x_342);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 1, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_353);
return x_355;
}
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_356 = lean_ctor_get(x_52, 0);
lean_inc(x_356);
lean_dec(x_52);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = lean_st_ref_take(x_3);
x_360 = lean_ctor_get(x_359, 1);
lean_inc_ref(x_360);
x_361 = lean_ctor_get(x_359, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_359, 3);
lean_inc(x_362);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 lean_ctor_release(x_359, 2);
 lean_ctor_release(x_359, 3);
 x_363 = x_359;
} else {
 lean_dec_ref(x_359);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(0, 4, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_358);
lean_ctor_set(x_364, 1, x_360);
lean_ctor_set(x_364, 2, x_361);
lean_ctor_set(x_364, 3, x_362);
x_365 = lean_st_ref_set(x_3, x_364);
x_366 = lean_ctor_get(x_357, 1);
lean_inc_ref(x_366);
lean_dec(x_357);
x_367 = lean_local_ctx_num_indices(x_366);
x_368 = lean_nat_dec_lt(x_35, x_367);
lean_dec(x_367);
if (x_368 == 0)
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_369; 
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_369 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
lean_dec_ref(x_369);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_370);
lean_inc(x_49);
x_371 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_49, x_370, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec_ref(x_371);
x_372 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_373, 0);
lean_inc(x_375);
lean_dec(x_373);
lean_inc(x_49);
x_376 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_376, 0, x_49);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_377 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_375, x_376, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
lean_dec_ref(x_377);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_st_ref_take(x_3);
x_382 = lean_ctor_get(x_381, 1);
lean_inc_ref(x_382);
x_383 = lean_ctor_get(x_381, 2);
lean_inc(x_383);
x_384 = lean_ctor_get(x_381, 3);
lean_inc(x_384);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 lean_ctor_release(x_381, 2);
 lean_ctor_release(x_381, 3);
 x_385 = x_381;
} else {
 lean_dec_ref(x_381);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(0, 4, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_380);
lean_ctor_set(x_386, 1, x_382);
lean_ctor_set(x_386, 2, x_383);
lean_ctor_set(x_386, 3, x_384);
x_387 = lean_st_ref_set(x_3, x_386);
x_388 = lean_unbox(x_379);
lean_dec(x_379);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_370);
lean_dec(x_49);
lean_dec(x_1);
x_389 = lean_st_ref_take(x_3);
x_390 = lean_ctor_get(x_389, 0);
lean_inc_ref(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc_ref(x_391);
x_392 = lean_ctor_get(x_389, 2);
lean_inc(x_392);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_393 = x_389;
} else {
 lean_dec_ref(x_389);
 x_393 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(0, 4, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_390);
lean_ctor_set(x_394, 1, x_391);
lean_ctor_set(x_394, 2, x_392);
lean_ctor_set(x_394, 3, x_37);
x_395 = lean_st_ref_set(x_3, x_394);
x_396 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 x_398 = x_396;
} else {
 lean_dec_ref(x_396);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_399 = lean_alloc_ctor(1, 1, 0);
} else {
 x_399 = x_374;
 lean_ctor_set_tag(x_399, 1);
}
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_2, 0, x_399);
if (lean_is_scalar(x_398)) {
 x_400 = lean_alloc_ctor(0, 1, 0);
} else {
 x_400 = x_398;
}
lean_ctor_set(x_400, 0, x_2);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_374);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_401 = lean_ctor_get(x_396, 0);
lean_inc(x_401);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 x_402 = x_396;
} else {
 lean_dec_ref(x_396);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 1, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_401);
return x_403;
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_34);
lean_inc(x_370);
x_404 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_404, 0, x_370);
x_405 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_405, 0, x_404);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_406 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_49, x_405, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec_ref(x_406);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; 
lean_dec(x_1);
lean_inc(x_370);
x_408 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_370, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_409 = x_408;
} else {
 lean_dec_ref(x_408);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_410 = lean_alloc_ctor(1, 1, 0);
} else {
 x_410 = x_374;
 lean_ctor_set_tag(x_410, 1);
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_32, 0, x_370);
lean_ctor_set(x_2, 0, x_410);
if (lean_is_scalar(x_409)) {
 x_411 = lean_alloc_ctor(0, 1, 0);
} else {
 x_411 = x_409;
}
lean_ctor_set(x_411, 0, x_2);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_374);
lean_dec(x_370);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_412 = lean_ctor_get(x_408, 0);
lean_inc(x_412);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_413 = x_408;
} else {
 lean_dec_ref(x_408);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 1, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_412);
return x_414;
}
}
else
{
lean_object* x_415; 
lean_dec(x_374);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_415 = lean_ctor_get(x_407, 0);
lean_inc(x_415);
lean_dec_ref(x_407);
lean_ctor_set(x_32, 1, x_415);
lean_ctor_set(x_32, 0, x_370);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_374);
lean_dec(x_370);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_417 = lean_ctor_get(x_406, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_418 = x_406;
} else {
 lean_dec_ref(x_406);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 1, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_417);
return x_419;
}
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_374);
lean_dec(x_370);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_420 = lean_ctor_get(x_377, 0);
lean_inc(x_420);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_421 = x_377;
} else {
 lean_dec_ref(x_377);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_420);
return x_422;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_370);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_423 = lean_ctor_get(x_371, 0);
lean_inc(x_423);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_424 = x_371;
} else {
 lean_dec_ref(x_371);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 1, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_426 = lean_ctor_get(x_369, 0);
lean_inc(x_426);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 x_427 = x_369;
} else {
 lean_dec_ref(x_369);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 1, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_426);
return x_428;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_429 = lean_ctor_get(x_45, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_45, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_431 = x_45;
} else {
 lean_dec_ref(x_45);
 x_431 = lean_box(0);
}
x_432 = lean_st_ref_take(x_3);
x_433 = lean_ctor_get(x_432, 1);
lean_inc_ref(x_433);
x_434 = lean_ctor_get(x_432, 2);
lean_inc(x_434);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_435 = x_432;
} else {
 lean_dec_ref(x_432);
 x_435 = lean_box(0);
}
lean_inc(x_47);
lean_ctor_set(x_36, 3, x_430);
lean_inc(x_37);
if (lean_is_scalar(x_431)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_431;
}
lean_ctor_set(x_436, 0, x_36);
lean_ctor_set(x_436, 1, x_37);
if (lean_is_scalar(x_435)) {
 x_437 = lean_alloc_ctor(0, 4, 0);
} else {
 x_437 = x_435;
}
lean_ctor_set(x_437, 0, x_429);
lean_ctor_set(x_437, 1, x_433);
lean_ctor_set(x_437, 2, x_434);
lean_ctor_set(x_437, 3, x_436);
x_438 = lean_st_ref_set(x_3, x_437);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
x_439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_439, 0, x_38);
lean_ctor_set(x_2, 0, x_439);
x_440 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_440, 0, x_2);
return x_440;
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_37);
lean_dec_ref(x_16);
x_441 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
lean_dec_ref(x_441);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
lean_dec(x_442);
lean_inc(x_34);
x_444 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_444, 0, x_49);
lean_closure_set(x_444, 1, x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_445 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_443, x_444, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
lean_dec_ref(x_445);
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
lean_dec(x_446);
x_448 = lean_st_ref_take(x_3);
x_449 = lean_ctor_get(x_448, 1);
lean_inc_ref(x_449);
x_450 = lean_ctor_get(x_448, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_448, 3);
lean_inc(x_451);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 lean_ctor_release(x_448, 2);
 lean_ctor_release(x_448, 3);
 x_452 = x_448;
} else {
 lean_dec_ref(x_448);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(0, 4, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_447);
lean_ctor_set(x_453, 1, x_449);
lean_ctor_set(x_453, 2, x_450);
lean_ctor_set(x_453, 3, x_451);
x_454 = lean_st_ref_set(x_3, x_453);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_456 = lean_ctor_get(x_445, 0);
lean_inc(x_456);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 x_457 = x_445;
} else {
 lean_dec_ref(x_445);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 1, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_456);
return x_458;
}
}
}
}
else
{
uint8_t x_459; 
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_459 = !lean_is_exclusive(x_52);
if (x_459 == 0)
{
return x_52;
}
else
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_ctor_get(x_52, 0);
lean_inc(x_460);
lean_dec(x_52);
x_461 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_461, 0, x_460);
return x_461;
}
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_462 = lean_ctor_get(x_38, 0);
x_463 = lean_ctor_get(x_36, 0);
x_464 = lean_ctor_get(x_36, 2);
x_465 = lean_ctor_get(x_36, 3);
x_466 = lean_ctor_get(x_36, 4);
x_467 = lean_ctor_get(x_36, 5);
lean_inc(x_467);
lean_inc(x_466);
lean_inc(x_465);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_36);
x_468 = lean_ctor_get(x_39, 0);
x_469 = lean_ctor_get(x_462, 0);
lean_inc(x_469);
lean_dec(x_462);
lean_inc(x_468);
x_470 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_470, 0, x_468);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_471 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_469, x_470, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 x_473 = x_471;
} else {
 lean_dec_ref(x_471);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_472, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_472, 1);
lean_inc(x_475);
lean_dec(x_472);
x_476 = lean_st_ref_take(x_3);
x_477 = lean_ctor_get(x_476, 1);
lean_inc_ref(x_477);
x_478 = lean_ctor_get(x_476, 2);
lean_inc(x_478);
x_479 = lean_ctor_get(x_476, 3);
lean_inc(x_479);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_480 = x_476;
} else {
 lean_dec_ref(x_476);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(0, 4, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_475);
lean_ctor_set(x_481, 1, x_477);
lean_ctor_set(x_481, 2, x_478);
lean_ctor_set(x_481, 3, x_479);
x_482 = lean_st_ref_set(x_3, x_481);
x_483 = lean_ctor_get(x_474, 1);
lean_inc_ref(x_483);
lean_dec(x_474);
x_484 = lean_local_ctx_num_indices(x_483);
x_485 = lean_nat_dec_lt(x_35, x_484);
lean_dec(x_484);
if (x_485 == 0)
{
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_486; 
lean_dec(x_473);
lean_inc(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_463);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_486 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_464, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
lean_dec_ref(x_486);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_487);
lean_inc(x_468);
x_488 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_468, x_487, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec_ref(x_488);
x_489 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 x_491 = x_489;
} else {
 lean_dec_ref(x_489);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_490, 0);
lean_inc(x_492);
lean_dec(x_490);
lean_inc(x_468);
x_493 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_493, 0, x_468);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_494 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_492, x_493, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
lean_dec_ref(x_494);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_498 = lean_st_ref_take(x_3);
x_499 = lean_ctor_get(x_498, 1);
lean_inc_ref(x_499);
x_500 = lean_ctor_get(x_498, 2);
lean_inc(x_500);
x_501 = lean_ctor_get(x_498, 3);
lean_inc(x_501);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 lean_ctor_release(x_498, 2);
 lean_ctor_release(x_498, 3);
 x_502 = x_498;
} else {
 lean_dec_ref(x_498);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(0, 4, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_497);
lean_ctor_set(x_503, 1, x_499);
lean_ctor_set(x_503, 2, x_500);
lean_ctor_set(x_503, 3, x_501);
x_504 = lean_st_ref_set(x_3, x_503);
x_505 = lean_unbox(x_496);
lean_dec(x_496);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_487);
lean_dec(x_468);
lean_dec(x_1);
x_506 = lean_st_ref_take(x_3);
x_507 = lean_ctor_get(x_506, 0);
lean_inc_ref(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc_ref(x_508);
x_509 = lean_ctor_get(x_506, 2);
lean_inc(x_509);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 lean_ctor_release(x_506, 2);
 lean_ctor_release(x_506, 3);
 x_510 = x_506;
} else {
 lean_dec_ref(x_506);
 x_510 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(0, 4, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_507);
lean_ctor_set(x_511, 1, x_508);
lean_ctor_set(x_511, 2, x_509);
lean_ctor_set(x_511, 3, x_37);
x_512 = lean_st_ref_set(x_3, x_511);
x_513 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 x_515 = x_513;
} else {
 lean_dec_ref(x_513);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_516 = lean_alloc_ctor(1, 1, 0);
} else {
 x_516 = x_491;
 lean_ctor_set_tag(x_516, 1);
}
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_2, 0, x_516);
if (lean_is_scalar(x_515)) {
 x_517 = lean_alloc_ctor(0, 1, 0);
} else {
 x_517 = x_515;
}
lean_ctor_set(x_517, 0, x_2);
return x_517;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_491);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_518 = lean_ctor_get(x_513, 0);
lean_inc(x_518);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 x_519 = x_513;
} else {
 lean_dec_ref(x_513);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 1, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_518);
return x_520;
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_34);
lean_inc(x_487);
x_521 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_521, 0, x_487);
x_522 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_522, 0, x_521);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_523 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_468, x_522, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
lean_dec_ref(x_523);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; 
lean_dec(x_1);
lean_inc(x_487);
x_525 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_487, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 x_526 = x_525;
} else {
 lean_dec_ref(x_525);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_527 = lean_alloc_ctor(1, 1, 0);
} else {
 x_527 = x_491;
 lean_ctor_set_tag(x_527, 1);
}
lean_ctor_set(x_527, 0, x_524);
lean_ctor_set(x_32, 0, x_487);
lean_ctor_set(x_2, 0, x_527);
if (lean_is_scalar(x_526)) {
 x_528 = lean_alloc_ctor(0, 1, 0);
} else {
 x_528 = x_526;
}
lean_ctor_set(x_528, 0, x_2);
return x_528;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_491);
lean_dec(x_487);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_529 = lean_ctor_get(x_525, 0);
lean_inc(x_529);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 x_530 = x_525;
} else {
 lean_dec_ref(x_525);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(1, 1, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_529);
return x_531;
}
}
else
{
lean_object* x_532; 
lean_dec(x_491);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_532 = lean_ctor_get(x_524, 0);
lean_inc(x_532);
lean_dec_ref(x_524);
lean_ctor_set(x_32, 1, x_532);
lean_ctor_set(x_32, 0, x_487);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_491);
lean_dec(x_487);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_534 = lean_ctor_get(x_523, 0);
lean_inc(x_534);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 x_535 = x_523;
} else {
 lean_dec_ref(x_523);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 1, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_534);
return x_536;
}
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_491);
lean_dec(x_487);
lean_dec(x_468);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_537 = lean_ctor_get(x_494, 0);
lean_inc(x_537);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 x_538 = x_494;
} else {
 lean_dec_ref(x_494);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 1, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_537);
return x_539;
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_487);
lean_dec(x_468);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_540 = lean_ctor_get(x_488, 0);
lean_inc(x_540);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 x_541 = x_488;
} else {
 lean_dec_ref(x_488);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 1, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_468);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_543 = lean_ctor_get(x_486, 0);
lean_inc(x_543);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_544 = x_486;
} else {
 lean_dec_ref(x_486);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 1, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_543);
return x_545;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_546 = lean_ctor_get(x_465, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_465, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_548 = x_465;
} else {
 lean_dec_ref(x_465);
 x_548 = lean_box(0);
}
x_549 = lean_st_ref_take(x_3);
x_550 = lean_ctor_get(x_549, 1);
lean_inc_ref(x_550);
x_551 = lean_ctor_get(x_549, 2);
lean_inc(x_551);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 lean_ctor_release(x_549, 2);
 lean_ctor_release(x_549, 3);
 x_552 = x_549;
} else {
 lean_dec_ref(x_549);
 x_552 = lean_box(0);
}
lean_inc(x_467);
x_553 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_553, 0, x_463);
lean_ctor_set(x_553, 1, x_39);
lean_ctor_set(x_553, 2, x_464);
lean_ctor_set(x_553, 3, x_547);
lean_ctor_set(x_553, 4, x_466);
lean_ctor_set(x_553, 5, x_467);
lean_inc(x_37);
if (lean_is_scalar(x_548)) {
 x_554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_554 = x_548;
}
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_37);
if (lean_is_scalar(x_552)) {
 x_555 = lean_alloc_ctor(0, 4, 0);
} else {
 x_555 = x_552;
}
lean_ctor_set(x_555, 0, x_546);
lean_ctor_set(x_555, 1, x_550);
lean_ctor_set(x_555, 2, x_551);
lean_ctor_set(x_555, 3, x_554);
x_556 = lean_st_ref_set(x_3, x_555);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_467);
x_557 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_557, 0, x_38);
lean_ctor_set(x_2, 0, x_557);
if (lean_is_scalar(x_473)) {
 x_558 = lean_alloc_ctor(0, 1, 0);
} else {
 x_558 = x_473;
}
lean_ctor_set(x_558, 0, x_2);
return x_558;
}
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_473);
lean_inc(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec_ref(x_464);
lean_dec(x_463);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_37);
lean_dec_ref(x_16);
x_559 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
lean_dec_ref(x_559);
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
lean_dec(x_560);
lean_inc(x_34);
x_562 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_562, 0, x_468);
lean_closure_set(x_562, 1, x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_563 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_561, x_562, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
lean_dec_ref(x_563);
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
lean_dec(x_564);
x_566 = lean_st_ref_take(x_3);
x_567 = lean_ctor_get(x_566, 1);
lean_inc_ref(x_567);
x_568 = lean_ctor_get(x_566, 2);
lean_inc(x_568);
x_569 = lean_ctor_get(x_566, 3);
lean_inc(x_569);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 lean_ctor_release(x_566, 2);
 lean_ctor_release(x_566, 3);
 x_570 = x_566;
} else {
 lean_dec_ref(x_566);
 x_570 = lean_box(0);
}
if (lean_is_scalar(x_570)) {
 x_571 = lean_alloc_ctor(0, 4, 0);
} else {
 x_571 = x_570;
}
lean_ctor_set(x_571, 0, x_565);
lean_ctor_set(x_571, 1, x_567);
lean_ctor_set(x_571, 2, x_568);
lean_ctor_set(x_571, 3, x_569);
x_572 = lean_st_ref_set(x_3, x_571);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_574 = lean_ctor_get(x_563, 0);
lean_inc(x_574);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 x_575 = x_563;
} else {
 lean_dec_ref(x_563);
 x_575 = lean_box(0);
}
if (lean_is_scalar(x_575)) {
 x_576 = lean_alloc_ctor(1, 1, 0);
} else {
 x_576 = x_575;
}
lean_ctor_set(x_576, 0, x_574);
return x_576;
}
}
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec_ref(x_464);
lean_dec(x_463);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_577 = lean_ctor_get(x_471, 0);
lean_inc(x_577);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 x_578 = x_471;
} else {
 lean_dec_ref(x_471);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(1, 1, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_577);
return x_579;
}
}
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_580 = lean_ctor_get(x_38, 0);
lean_inc(x_580);
lean_dec(x_38);
x_581 = lean_ctor_get(x_36, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_36, 2);
lean_inc_ref(x_582);
x_583 = lean_ctor_get(x_36, 3);
lean_inc(x_583);
x_584 = lean_ctor_get(x_36, 4);
lean_inc_ref(x_584);
x_585 = lean_ctor_get(x_36, 5);
lean_inc(x_585);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 x_586 = x_36;
} else {
 lean_dec_ref(x_36);
 x_586 = lean_box(0);
}
x_587 = lean_ctor_get(x_39, 0);
x_588 = lean_ctor_get(x_580, 0);
lean_inc(x_588);
lean_dec(x_580);
lean_inc(x_587);
x_589 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_589, 0, x_587);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_590 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_588, x_589, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 x_592 = x_590;
} else {
 lean_dec_ref(x_590);
 x_592 = lean_box(0);
}
x_593 = lean_ctor_get(x_591, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_591, 1);
lean_inc(x_594);
lean_dec(x_591);
x_595 = lean_st_ref_take(x_3);
x_596 = lean_ctor_get(x_595, 1);
lean_inc_ref(x_596);
x_597 = lean_ctor_get(x_595, 2);
lean_inc(x_597);
x_598 = lean_ctor_get(x_595, 3);
lean_inc(x_598);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 lean_ctor_release(x_595, 2);
 lean_ctor_release(x_595, 3);
 x_599 = x_595;
} else {
 lean_dec_ref(x_595);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(0, 4, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_594);
lean_ctor_set(x_600, 1, x_596);
lean_ctor_set(x_600, 2, x_597);
lean_ctor_set(x_600, 3, x_598);
x_601 = lean_st_ref_set(x_3, x_600);
x_602 = lean_ctor_get(x_593, 1);
lean_inc_ref(x_602);
lean_dec(x_593);
x_603 = lean_local_ctx_num_indices(x_602);
x_604 = lean_nat_dec_lt(x_35, x_603);
lean_dec(x_603);
if (x_604 == 0)
{
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_605; 
lean_dec(x_592);
lean_inc(x_587);
lean_dec(x_586);
lean_dec(x_585);
lean_dec_ref(x_584);
lean_dec(x_581);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_605 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_582, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
lean_dec_ref(x_605);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_606);
lean_inc(x_587);
x_607 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_587, x_606, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec_ref(x_607);
x_608 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 x_610 = x_608;
} else {
 lean_dec_ref(x_608);
 x_610 = lean_box(0);
}
x_611 = lean_ctor_get(x_609, 0);
lean_inc(x_611);
lean_dec(x_609);
lean_inc(x_587);
x_612 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_612, 0, x_587);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_613 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_611, x_612, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
lean_dec_ref(x_613);
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
x_617 = lean_st_ref_take(x_3);
x_618 = lean_ctor_get(x_617, 1);
lean_inc_ref(x_618);
x_619 = lean_ctor_get(x_617, 2);
lean_inc(x_619);
x_620 = lean_ctor_get(x_617, 3);
lean_inc(x_620);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 lean_ctor_release(x_617, 2);
 lean_ctor_release(x_617, 3);
 x_621 = x_617;
} else {
 lean_dec_ref(x_617);
 x_621 = lean_box(0);
}
if (lean_is_scalar(x_621)) {
 x_622 = lean_alloc_ctor(0, 4, 0);
} else {
 x_622 = x_621;
}
lean_ctor_set(x_622, 0, x_616);
lean_ctor_set(x_622, 1, x_618);
lean_ctor_set(x_622, 2, x_619);
lean_ctor_set(x_622, 3, x_620);
x_623 = lean_st_ref_set(x_3, x_622);
x_624 = lean_unbox(x_615);
lean_dec(x_615);
if (x_624 == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_606);
lean_dec(x_587);
lean_dec(x_1);
x_625 = lean_st_ref_take(x_3);
x_626 = lean_ctor_get(x_625, 0);
lean_inc_ref(x_626);
x_627 = lean_ctor_get(x_625, 1);
lean_inc_ref(x_627);
x_628 = lean_ctor_get(x_625, 2);
lean_inc(x_628);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 lean_ctor_release(x_625, 2);
 lean_ctor_release(x_625, 3);
 x_629 = x_625;
} else {
 lean_dec_ref(x_625);
 x_629 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(0, 4, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_626);
lean_ctor_set(x_630, 1, x_627);
lean_ctor_set(x_630, 2, x_628);
lean_ctor_set(x_630, 3, x_37);
x_631 = lean_st_ref_set(x_3, x_630);
x_632 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 x_634 = x_632;
} else {
 lean_dec_ref(x_632);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_635 = lean_alloc_ctor(1, 1, 0);
} else {
 x_635 = x_610;
 lean_ctor_set_tag(x_635, 1);
}
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_2, 0, x_635);
if (lean_is_scalar(x_634)) {
 x_636 = lean_alloc_ctor(0, 1, 0);
} else {
 x_636 = x_634;
}
lean_ctor_set(x_636, 0, x_2);
return x_636;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_610);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_637 = lean_ctor_get(x_632, 0);
lean_inc(x_637);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 x_638 = x_632;
} else {
 lean_dec_ref(x_632);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 1, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_34);
lean_inc(x_606);
x_640 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_640, 0, x_606);
x_641 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_641, 0, x_640);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_642 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_587, x_641, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_643; 
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
lean_dec_ref(x_642);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; 
lean_dec(x_1);
lean_inc(x_606);
x_644 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_606, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 x_645 = x_644;
} else {
 lean_dec_ref(x_644);
 x_645 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_646 = lean_alloc_ctor(1, 1, 0);
} else {
 x_646 = x_610;
 lean_ctor_set_tag(x_646, 1);
}
lean_ctor_set(x_646, 0, x_643);
lean_ctor_set(x_32, 0, x_606);
lean_ctor_set(x_2, 0, x_646);
if (lean_is_scalar(x_645)) {
 x_647 = lean_alloc_ctor(0, 1, 0);
} else {
 x_647 = x_645;
}
lean_ctor_set(x_647, 0, x_2);
return x_647;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_610);
lean_dec(x_606);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_648 = lean_ctor_get(x_644, 0);
lean_inc(x_648);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 x_649 = x_644;
} else {
 lean_dec_ref(x_644);
 x_649 = lean_box(0);
}
if (lean_is_scalar(x_649)) {
 x_650 = lean_alloc_ctor(1, 1, 0);
} else {
 x_650 = x_649;
}
lean_ctor_set(x_650, 0, x_648);
return x_650;
}
}
else
{
lean_object* x_651; 
lean_dec(x_610);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_651 = lean_ctor_get(x_643, 0);
lean_inc(x_651);
lean_dec_ref(x_643);
lean_ctor_set(x_32, 1, x_651);
lean_ctor_set(x_32, 0, x_606);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_610);
lean_dec(x_606);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_653 = lean_ctor_get(x_642, 0);
lean_inc(x_653);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 x_654 = x_642;
} else {
 lean_dec_ref(x_642);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(1, 1, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_653);
return x_655;
}
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_610);
lean_dec(x_606);
lean_dec(x_587);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_656 = lean_ctor_get(x_613, 0);
lean_inc(x_656);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 x_657 = x_613;
} else {
 lean_dec_ref(x_613);
 x_657 = lean_box(0);
}
if (lean_is_scalar(x_657)) {
 x_658 = lean_alloc_ctor(1, 1, 0);
} else {
 x_658 = x_657;
}
lean_ctor_set(x_658, 0, x_656);
return x_658;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_606);
lean_dec(x_587);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_659 = lean_ctor_get(x_607, 0);
lean_inc(x_659);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 x_660 = x_607;
} else {
 lean_dec_ref(x_607);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 1, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_659);
return x_661;
}
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_587);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_662 = lean_ctor_get(x_605, 0);
lean_inc(x_662);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 x_663 = x_605;
} else {
 lean_dec_ref(x_605);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 1, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_662);
return x_664;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_665 = lean_ctor_get(x_583, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_583, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_667 = x_583;
} else {
 lean_dec_ref(x_583);
 x_667 = lean_box(0);
}
x_668 = lean_st_ref_take(x_3);
x_669 = lean_ctor_get(x_668, 1);
lean_inc_ref(x_669);
x_670 = lean_ctor_get(x_668, 2);
lean_inc(x_670);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 lean_ctor_release(x_668, 2);
 lean_ctor_release(x_668, 3);
 x_671 = x_668;
} else {
 lean_dec_ref(x_668);
 x_671 = lean_box(0);
}
lean_inc(x_585);
if (lean_is_scalar(x_586)) {
 x_672 = lean_alloc_ctor(0, 6, 0);
} else {
 x_672 = x_586;
}
lean_ctor_set(x_672, 0, x_581);
lean_ctor_set(x_672, 1, x_39);
lean_ctor_set(x_672, 2, x_582);
lean_ctor_set(x_672, 3, x_666);
lean_ctor_set(x_672, 4, x_584);
lean_ctor_set(x_672, 5, x_585);
lean_inc(x_37);
if (lean_is_scalar(x_667)) {
 x_673 = lean_alloc_ctor(1, 2, 0);
} else {
 x_673 = x_667;
}
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_37);
if (lean_is_scalar(x_671)) {
 x_674 = lean_alloc_ctor(0, 4, 0);
} else {
 x_674 = x_671;
}
lean_ctor_set(x_674, 0, x_665);
lean_ctor_set(x_674, 1, x_669);
lean_ctor_set(x_674, 2, x_670);
lean_ctor_set(x_674, 3, x_673);
x_675 = lean_st_ref_set(x_3, x_674);
lean_dec(x_3);
x_676 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_676, 0, x_585);
x_677 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_2, 0, x_677);
if (lean_is_scalar(x_592)) {
 x_678 = lean_alloc_ctor(0, 1, 0);
} else {
 x_678 = x_592;
}
lean_ctor_set(x_678, 0, x_2);
return x_678;
}
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_592);
lean_inc(x_587);
lean_dec(x_586);
lean_dec(x_585);
lean_dec_ref(x_584);
lean_dec(x_583);
lean_dec_ref(x_582);
lean_dec(x_581);
lean_dec_ref(x_39);
lean_inc(x_37);
lean_dec_ref(x_16);
x_679 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
lean_dec_ref(x_679);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
lean_dec(x_680);
lean_inc(x_34);
x_682 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_682, 0, x_587);
lean_closure_set(x_682, 1, x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_683 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_681, x_682, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
lean_dec_ref(x_683);
x_685 = lean_ctor_get(x_684, 1);
lean_inc(x_685);
lean_dec(x_684);
x_686 = lean_st_ref_take(x_3);
x_687 = lean_ctor_get(x_686, 1);
lean_inc_ref(x_687);
x_688 = lean_ctor_get(x_686, 2);
lean_inc(x_688);
x_689 = lean_ctor_get(x_686, 3);
lean_inc(x_689);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 lean_ctor_release(x_686, 2);
 lean_ctor_release(x_686, 3);
 x_690 = x_686;
} else {
 lean_dec_ref(x_686);
 x_690 = lean_box(0);
}
if (lean_is_scalar(x_690)) {
 x_691 = lean_alloc_ctor(0, 4, 0);
} else {
 x_691 = x_690;
}
lean_ctor_set(x_691, 0, x_685);
lean_ctor_set(x_691, 1, x_687);
lean_ctor_set(x_691, 2, x_688);
lean_ctor_set(x_691, 3, x_689);
x_692 = lean_st_ref_set(x_3, x_691);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_694 = lean_ctor_get(x_683, 0);
lean_inc(x_694);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 x_695 = x_683;
} else {
 lean_dec_ref(x_683);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 1, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_694);
return x_696;
}
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_586);
lean_dec(x_585);
lean_dec_ref(x_584);
lean_dec(x_583);
lean_dec_ref(x_582);
lean_dec(x_581);
lean_dec_ref(x_39);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_697 = lean_ctor_get(x_590, 0);
lean_inc(x_697);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 x_698 = x_590;
} else {
 lean_dec_ref(x_590);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 1, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_697);
return x_699;
}
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_700 = lean_ctor_get(x_32, 0);
x_701 = lean_ctor_get(x_32, 1);
lean_inc(x_701);
lean_inc(x_700);
lean_dec(x_32);
x_702 = lean_ctor_get(x_16, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_16, 1);
x_704 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_705 = lean_ctor_get(x_702, 1);
lean_inc_ref(x_705);
x_706 = lean_ctor_get(x_704, 0);
lean_inc(x_706);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 x_707 = x_704;
} else {
 lean_dec_ref(x_704);
 x_707 = lean_box(0);
}
x_708 = lean_ctor_get(x_702, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_702, 2);
lean_inc_ref(x_709);
x_710 = lean_ctor_get(x_702, 3);
lean_inc(x_710);
x_711 = lean_ctor_get(x_702, 4);
lean_inc_ref(x_711);
x_712 = lean_ctor_get(x_702, 5);
lean_inc(x_712);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 lean_ctor_release(x_702, 2);
 lean_ctor_release(x_702, 3);
 lean_ctor_release(x_702, 4);
 lean_ctor_release(x_702, 5);
 x_713 = x_702;
} else {
 lean_dec_ref(x_702);
 x_713 = lean_box(0);
}
x_714 = lean_ctor_get(x_705, 0);
x_715 = lean_ctor_get(x_706, 0);
lean_inc(x_715);
lean_dec(x_706);
lean_inc(x_714);
x_716 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_716, 0, x_714);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_717 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_715, x_716, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; uint8_t x_731; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 x_719 = x_717;
} else {
 lean_dec_ref(x_717);
 x_719 = lean_box(0);
}
x_720 = lean_ctor_get(x_718, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_718, 1);
lean_inc(x_721);
lean_dec(x_718);
x_722 = lean_st_ref_take(x_3);
x_723 = lean_ctor_get(x_722, 1);
lean_inc_ref(x_723);
x_724 = lean_ctor_get(x_722, 2);
lean_inc(x_724);
x_725 = lean_ctor_get(x_722, 3);
lean_inc(x_725);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 lean_ctor_release(x_722, 1);
 lean_ctor_release(x_722, 2);
 lean_ctor_release(x_722, 3);
 x_726 = x_722;
} else {
 lean_dec_ref(x_722);
 x_726 = lean_box(0);
}
if (lean_is_scalar(x_726)) {
 x_727 = lean_alloc_ctor(0, 4, 0);
} else {
 x_727 = x_726;
}
lean_ctor_set(x_727, 0, x_721);
lean_ctor_set(x_727, 1, x_723);
lean_ctor_set(x_727, 2, x_724);
lean_ctor_set(x_727, 3, x_725);
x_728 = lean_st_ref_set(x_3, x_727);
x_729 = lean_ctor_get(x_720, 1);
lean_inc_ref(x_729);
lean_dec(x_720);
x_730 = lean_local_ctx_num_indices(x_729);
x_731 = lean_nat_dec_lt(x_701, x_730);
lean_dec(x_730);
if (x_731 == 0)
{
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_732; 
lean_dec(x_719);
lean_inc(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec(x_708);
lean_dec(x_707);
lean_dec_ref(x_705);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_732 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_709, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; lean_object* x_734; 
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
lean_dec_ref(x_732);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_733);
lean_inc(x_714);
x_734 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_714, x_733, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec_ref(x_734);
x_735 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 x_737 = x_735;
} else {
 lean_dec_ref(x_735);
 x_737 = lean_box(0);
}
x_738 = lean_ctor_get(x_736, 0);
lean_inc(x_738);
lean_dec(x_736);
lean_inc(x_714);
x_739 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_739, 0, x_714);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_740 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_738, x_739, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_740) == 0)
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; 
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
lean_dec_ref(x_740);
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
x_744 = lean_st_ref_take(x_3);
x_745 = lean_ctor_get(x_744, 1);
lean_inc_ref(x_745);
x_746 = lean_ctor_get(x_744, 2);
lean_inc(x_746);
x_747 = lean_ctor_get(x_744, 3);
lean_inc(x_747);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 lean_ctor_release(x_744, 1);
 lean_ctor_release(x_744, 2);
 lean_ctor_release(x_744, 3);
 x_748 = x_744;
} else {
 lean_dec_ref(x_744);
 x_748 = lean_box(0);
}
if (lean_is_scalar(x_748)) {
 x_749 = lean_alloc_ctor(0, 4, 0);
} else {
 x_749 = x_748;
}
lean_ctor_set(x_749, 0, x_743);
lean_ctor_set(x_749, 1, x_745);
lean_ctor_set(x_749, 2, x_746);
lean_ctor_set(x_749, 3, x_747);
x_750 = lean_st_ref_set(x_3, x_749);
x_751 = lean_unbox(x_742);
lean_dec(x_742);
if (x_751 == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
lean_dec(x_733);
lean_dec(x_714);
lean_dec(x_1);
x_752 = lean_st_ref_take(x_3);
x_753 = lean_ctor_get(x_752, 0);
lean_inc_ref(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc_ref(x_754);
x_755 = lean_ctor_get(x_752, 2);
lean_inc(x_755);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 lean_ctor_release(x_752, 2);
 lean_ctor_release(x_752, 3);
 x_756 = x_752;
} else {
 lean_dec_ref(x_752);
 x_756 = lean_box(0);
}
lean_inc(x_703);
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(0, 4, 0);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_753);
lean_ctor_set(x_757, 1, x_754);
lean_ctor_set(x_757, 2, x_755);
lean_ctor_set(x_757, 3, x_703);
x_758 = lean_st_ref_set(x_3, x_757);
x_759 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 x_761 = x_759;
} else {
 lean_dec_ref(x_759);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_762 = lean_alloc_ctor(1, 1, 0);
} else {
 x_762 = x_737;
 lean_ctor_set_tag(x_762, 1);
}
lean_ctor_set(x_762, 0, x_760);
x_763 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_763, 0, x_700);
lean_ctor_set(x_763, 1, x_701);
lean_ctor_set(x_13, 1, x_763);
lean_ctor_set(x_2, 0, x_762);
if (lean_is_scalar(x_761)) {
 x_764 = lean_alloc_ctor(0, 1, 0);
} else {
 x_764 = x_761;
}
lean_ctor_set(x_764, 0, x_2);
return x_764;
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; 
lean_dec(x_737);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_765 = lean_ctor_get(x_759, 0);
lean_inc(x_765);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 x_766 = x_759;
} else {
 lean_dec_ref(x_759);
 x_766 = lean_box(0);
}
if (lean_is_scalar(x_766)) {
 x_767 = lean_alloc_ctor(1, 1, 0);
} else {
 x_767 = x_766;
}
lean_ctor_set(x_767, 0, x_765);
return x_767;
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_700);
lean_inc(x_733);
x_768 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_768, 0, x_733);
x_769 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_769, 0, x_768);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_770 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_714, x_769, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_770) == 0)
{
lean_object* x_771; 
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
lean_dec_ref(x_770);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; 
lean_dec(x_1);
lean_inc(x_733);
x_772 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_733, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_772) == 0)
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 x_773 = x_772;
} else {
 lean_dec_ref(x_772);
 x_773 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_774 = lean_alloc_ctor(1, 1, 0);
} else {
 x_774 = x_737;
 lean_ctor_set_tag(x_774, 1);
}
lean_ctor_set(x_774, 0, x_771);
x_775 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_775, 0, x_733);
lean_ctor_set(x_775, 1, x_701);
lean_ctor_set(x_13, 1, x_775);
lean_ctor_set(x_2, 0, x_774);
if (lean_is_scalar(x_773)) {
 x_776 = lean_alloc_ctor(0, 1, 0);
} else {
 x_776 = x_773;
}
lean_ctor_set(x_776, 0, x_2);
return x_776;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
lean_dec(x_737);
lean_dec(x_733);
lean_dec(x_701);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_777 = lean_ctor_get(x_772, 0);
lean_inc(x_777);
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 x_778 = x_772;
} else {
 lean_dec_ref(x_772);
 x_778 = lean_box(0);
}
if (lean_is_scalar(x_778)) {
 x_779 = lean_alloc_ctor(1, 1, 0);
} else {
 x_779 = x_778;
}
lean_ctor_set(x_779, 0, x_777);
return x_779;
}
}
else
{
lean_object* x_780; lean_object* x_781; 
lean_dec(x_737);
lean_inc(x_703);
lean_dec(x_701);
lean_dec_ref(x_16);
x_780 = lean_ctor_get(x_771, 0);
lean_inc(x_780);
lean_dec_ref(x_771);
x_781 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_781, 0, x_733);
lean_ctor_set(x_781, 1, x_780);
lean_ctor_set(x_13, 1, x_781);
lean_ctor_set(x_13, 0, x_703);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
lean_dec(x_737);
lean_dec(x_733);
lean_dec(x_701);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_783 = lean_ctor_get(x_770, 0);
lean_inc(x_783);
if (lean_is_exclusive(x_770)) {
 lean_ctor_release(x_770, 0);
 x_784 = x_770;
} else {
 lean_dec_ref(x_770);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(1, 1, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_783);
return x_785;
}
}
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
lean_dec(x_737);
lean_dec(x_733);
lean_dec(x_714);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_786 = lean_ctor_get(x_740, 0);
lean_inc(x_786);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 x_787 = x_740;
} else {
 lean_dec_ref(x_740);
 x_787 = lean_box(0);
}
if (lean_is_scalar(x_787)) {
 x_788 = lean_alloc_ctor(1, 1, 0);
} else {
 x_788 = x_787;
}
lean_ctor_set(x_788, 0, x_786);
return x_788;
}
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
lean_dec(x_733);
lean_dec(x_714);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_789 = lean_ctor_get(x_734, 0);
lean_inc(x_789);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 x_790 = x_734;
} else {
 lean_dec_ref(x_734);
 x_790 = lean_box(0);
}
if (lean_is_scalar(x_790)) {
 x_791 = lean_alloc_ctor(1, 1, 0);
} else {
 x_791 = x_790;
}
lean_ctor_set(x_791, 0, x_789);
return x_791;
}
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_714);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_792 = lean_ctor_get(x_732, 0);
lean_inc(x_792);
if (lean_is_exclusive(x_732)) {
 lean_ctor_release(x_732, 0);
 x_793 = x_732;
} else {
 lean_dec_ref(x_732);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 1, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_792);
return x_794;
}
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_795 = lean_ctor_get(x_710, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_710, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_797 = x_710;
} else {
 lean_dec_ref(x_710);
 x_797 = lean_box(0);
}
x_798 = lean_st_ref_take(x_3);
x_799 = lean_ctor_get(x_798, 1);
lean_inc_ref(x_799);
x_800 = lean_ctor_get(x_798, 2);
lean_inc(x_800);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 lean_ctor_release(x_798, 2);
 lean_ctor_release(x_798, 3);
 x_801 = x_798;
} else {
 lean_dec_ref(x_798);
 x_801 = lean_box(0);
}
lean_inc(x_712);
if (lean_is_scalar(x_713)) {
 x_802 = lean_alloc_ctor(0, 6, 0);
} else {
 x_802 = x_713;
}
lean_ctor_set(x_802, 0, x_708);
lean_ctor_set(x_802, 1, x_705);
lean_ctor_set(x_802, 2, x_709);
lean_ctor_set(x_802, 3, x_796);
lean_ctor_set(x_802, 4, x_711);
lean_ctor_set(x_802, 5, x_712);
lean_inc(x_703);
if (lean_is_scalar(x_797)) {
 x_803 = lean_alloc_ctor(1, 2, 0);
} else {
 x_803 = x_797;
}
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_703);
if (lean_is_scalar(x_801)) {
 x_804 = lean_alloc_ctor(0, 4, 0);
} else {
 x_804 = x_801;
}
lean_ctor_set(x_804, 0, x_795);
lean_ctor_set(x_804, 1, x_799);
lean_ctor_set(x_804, 2, x_800);
lean_ctor_set(x_804, 3, x_803);
x_805 = lean_st_ref_set(x_3, x_804);
lean_dec(x_3);
if (lean_is_scalar(x_707)) {
 x_806 = lean_alloc_ctor(1, 1, 0);
} else {
 x_806 = x_707;
 lean_ctor_set_tag(x_806, 1);
}
lean_ctor_set(x_806, 0, x_712);
x_807 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_807, 0, x_806);
x_808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_808, 0, x_700);
lean_ctor_set(x_808, 1, x_701);
lean_ctor_set(x_13, 1, x_808);
lean_ctor_set(x_2, 0, x_807);
if (lean_is_scalar(x_719)) {
 x_809 = lean_alloc_ctor(0, 1, 0);
} else {
 x_809 = x_719;
}
lean_ctor_set(x_809, 0, x_2);
return x_809;
}
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_dec(x_719);
lean_inc(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec(x_707);
lean_dec_ref(x_705);
lean_inc(x_703);
lean_dec_ref(x_16);
x_810 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
lean_dec_ref(x_810);
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
lean_dec(x_811);
lean_inc(x_700);
x_813 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_813, 0, x_714);
lean_closure_set(x_813, 1, x_700);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_814 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_812, x_813, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_815 = lean_ctor_get(x_814, 0);
lean_inc(x_815);
lean_dec_ref(x_814);
x_816 = lean_ctor_get(x_815, 1);
lean_inc(x_816);
lean_dec(x_815);
x_817 = lean_st_ref_take(x_3);
x_818 = lean_ctor_get(x_817, 1);
lean_inc_ref(x_818);
x_819 = lean_ctor_get(x_817, 2);
lean_inc(x_819);
x_820 = lean_ctor_get(x_817, 3);
lean_inc(x_820);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 lean_ctor_release(x_817, 2);
 lean_ctor_release(x_817, 3);
 x_821 = x_817;
} else {
 lean_dec_ref(x_817);
 x_821 = lean_box(0);
}
if (lean_is_scalar(x_821)) {
 x_822 = lean_alloc_ctor(0, 4, 0);
} else {
 x_822 = x_821;
}
lean_ctor_set(x_822, 0, x_816);
lean_ctor_set(x_822, 1, x_818);
lean_ctor_set(x_822, 2, x_819);
lean_ctor_set(x_822, 3, x_820);
x_823 = lean_st_ref_set(x_3, x_822);
x_824 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_824, 0, x_700);
lean_ctor_set(x_824, 1, x_701);
lean_ctor_set(x_13, 1, x_824);
lean_ctor_set(x_13, 0, x_703);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
lean_dec(x_703);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_826 = lean_ctor_get(x_814, 0);
lean_inc(x_826);
if (lean_is_exclusive(x_814)) {
 lean_ctor_release(x_814, 0);
 x_827 = x_814;
} else {
 lean_dec_ref(x_814);
 x_827 = lean_box(0);
}
if (lean_is_scalar(x_827)) {
 x_828 = lean_alloc_ctor(1, 1, 0);
} else {
 x_828 = x_827;
}
lean_ctor_set(x_828, 0, x_826);
return x_828;
}
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; 
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec(x_707);
lean_dec_ref(x_705);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_829 = lean_ctor_get(x_717, 0);
lean_inc(x_829);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 x_830 = x_717;
} else {
 lean_dec_ref(x_717);
 x_830 = lean_box(0);
}
if (lean_is_scalar(x_830)) {
 x_831 = lean_alloc_ctor(1, 1, 0);
} else {
 x_831 = x_830;
}
lean_ctor_set(x_831, 0, x_829);
return x_831;
}
}
}
}
else
{
lean_object* x_832; lean_object* x_833; 
x_832 = lean_ctor_get(x_13, 1);
x_833 = lean_ctor_get(x_13, 0);
lean_inc(x_832);
lean_inc(x_833);
lean_dec(x_13);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_834 = lean_ctor_get(x_832, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_832, 1);
lean_inc(x_835);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_836 = x_832;
} else {
 lean_dec_ref(x_832);
 x_836 = lean_box(0);
}
x_837 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_3);
lean_dec(x_3);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 x_838 = x_837;
} else {
 lean_dec_ref(x_837);
 x_838 = lean_box(0);
}
x_839 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
if (lean_is_scalar(x_836)) {
 x_840 = lean_alloc_ctor(0, 2, 0);
} else {
 x_840 = x_836;
}
lean_ctor_set(x_840, 0, x_834);
lean_ctor_set(x_840, 1, x_835);
x_841 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_841, 0, x_833);
lean_ctor_set(x_841, 1, x_840);
lean_ctor_set(x_2, 1, x_841);
lean_ctor_set(x_2, 0, x_839);
if (lean_is_scalar(x_838)) {
 x_842 = lean_alloc_ctor(0, 1, 0);
} else {
 x_842 = x_838;
}
lean_ctor_set(x_842, 0, x_2);
return x_842;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_843 = lean_ctor_get(x_832, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_832, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_845 = x_832;
} else {
 lean_dec_ref(x_832);
 x_845 = lean_box(0);
}
x_846 = lean_ctor_get(x_833, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_833, 1);
x_848 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_849 = lean_ctor_get(x_846, 1);
lean_inc_ref(x_849);
x_850 = lean_ctor_get(x_848, 0);
lean_inc(x_850);
if (lean_is_exclusive(x_848)) {
 lean_ctor_release(x_848, 0);
 x_851 = x_848;
} else {
 lean_dec_ref(x_848);
 x_851 = lean_box(0);
}
x_852 = lean_ctor_get(x_846, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_846, 2);
lean_inc_ref(x_853);
x_854 = lean_ctor_get(x_846, 3);
lean_inc(x_854);
x_855 = lean_ctor_get(x_846, 4);
lean_inc_ref(x_855);
x_856 = lean_ctor_get(x_846, 5);
lean_inc(x_856);
if (lean_is_exclusive(x_846)) {
 lean_ctor_release(x_846, 0);
 lean_ctor_release(x_846, 1);
 lean_ctor_release(x_846, 2);
 lean_ctor_release(x_846, 3);
 lean_ctor_release(x_846, 4);
 lean_ctor_release(x_846, 5);
 x_857 = x_846;
} else {
 lean_dec_ref(x_846);
 x_857 = lean_box(0);
}
x_858 = lean_ctor_get(x_849, 0);
x_859 = lean_ctor_get(x_850, 0);
lean_inc(x_859);
lean_dec(x_850);
lean_inc(x_858);
x_860 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_860, 0, x_858);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_861 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_859, x_860, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; uint8_t x_875; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
if (lean_is_exclusive(x_861)) {
 lean_ctor_release(x_861, 0);
 x_863 = x_861;
} else {
 lean_dec_ref(x_861);
 x_863 = lean_box(0);
}
x_864 = lean_ctor_get(x_862, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_862, 1);
lean_inc(x_865);
lean_dec(x_862);
x_866 = lean_st_ref_take(x_3);
x_867 = lean_ctor_get(x_866, 1);
lean_inc_ref(x_867);
x_868 = lean_ctor_get(x_866, 2);
lean_inc(x_868);
x_869 = lean_ctor_get(x_866, 3);
lean_inc(x_869);
if (lean_is_exclusive(x_866)) {
 lean_ctor_release(x_866, 0);
 lean_ctor_release(x_866, 1);
 lean_ctor_release(x_866, 2);
 lean_ctor_release(x_866, 3);
 x_870 = x_866;
} else {
 lean_dec_ref(x_866);
 x_870 = lean_box(0);
}
if (lean_is_scalar(x_870)) {
 x_871 = lean_alloc_ctor(0, 4, 0);
} else {
 x_871 = x_870;
}
lean_ctor_set(x_871, 0, x_865);
lean_ctor_set(x_871, 1, x_867);
lean_ctor_set(x_871, 2, x_868);
lean_ctor_set(x_871, 3, x_869);
x_872 = lean_st_ref_set(x_3, x_871);
x_873 = lean_ctor_get(x_864, 1);
lean_inc_ref(x_873);
lean_dec(x_864);
x_874 = lean_local_ctx_num_indices(x_873);
x_875 = lean_nat_dec_lt(x_844, x_874);
lean_dec(x_874);
if (x_875 == 0)
{
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_876; 
lean_dec(x_863);
lean_inc(x_858);
lean_dec(x_857);
lean_dec(x_856);
lean_dec_ref(x_855);
lean_dec(x_852);
lean_dec(x_851);
lean_dec_ref(x_849);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_876 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_853, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
lean_dec_ref(x_876);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_877);
lean_inc(x_858);
x_878 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_858, x_877, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec_ref(x_878);
x_879 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_880 = lean_ctor_get(x_879, 0);
lean_inc(x_880);
if (lean_is_exclusive(x_879)) {
 lean_ctor_release(x_879, 0);
 x_881 = x_879;
} else {
 lean_dec_ref(x_879);
 x_881 = lean_box(0);
}
x_882 = lean_ctor_get(x_880, 0);
lean_inc(x_882);
lean_dec(x_880);
lean_inc(x_858);
x_883 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_883, 0, x_858);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_884 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_882, x_883, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; uint8_t x_895; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
lean_dec_ref(x_884);
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
lean_dec(x_885);
x_888 = lean_st_ref_take(x_3);
x_889 = lean_ctor_get(x_888, 1);
lean_inc_ref(x_889);
x_890 = lean_ctor_get(x_888, 2);
lean_inc(x_890);
x_891 = lean_ctor_get(x_888, 3);
lean_inc(x_891);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 lean_ctor_release(x_888, 2);
 lean_ctor_release(x_888, 3);
 x_892 = x_888;
} else {
 lean_dec_ref(x_888);
 x_892 = lean_box(0);
}
if (lean_is_scalar(x_892)) {
 x_893 = lean_alloc_ctor(0, 4, 0);
} else {
 x_893 = x_892;
}
lean_ctor_set(x_893, 0, x_887);
lean_ctor_set(x_893, 1, x_889);
lean_ctor_set(x_893, 2, x_890);
lean_ctor_set(x_893, 3, x_891);
x_894 = lean_st_ref_set(x_3, x_893);
x_895 = lean_unbox(x_886);
lean_dec(x_886);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; 
lean_dec(x_877);
lean_dec(x_858);
lean_dec(x_1);
x_896 = lean_st_ref_take(x_3);
x_897 = lean_ctor_get(x_896, 0);
lean_inc_ref(x_897);
x_898 = lean_ctor_get(x_896, 1);
lean_inc_ref(x_898);
x_899 = lean_ctor_get(x_896, 2);
lean_inc(x_899);
if (lean_is_exclusive(x_896)) {
 lean_ctor_release(x_896, 0);
 lean_ctor_release(x_896, 1);
 lean_ctor_release(x_896, 2);
 lean_ctor_release(x_896, 3);
 x_900 = x_896;
} else {
 lean_dec_ref(x_896);
 x_900 = lean_box(0);
}
lean_inc(x_847);
if (lean_is_scalar(x_900)) {
 x_901 = lean_alloc_ctor(0, 4, 0);
} else {
 x_901 = x_900;
}
lean_ctor_set(x_901, 0, x_897);
lean_ctor_set(x_901, 1, x_898);
lean_ctor_set(x_901, 2, x_899);
lean_ctor_set(x_901, 3, x_847);
x_902 = lean_st_ref_set(x_3, x_901);
x_903 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 x_905 = x_903;
} else {
 lean_dec_ref(x_903);
 x_905 = lean_box(0);
}
if (lean_is_scalar(x_881)) {
 x_906 = lean_alloc_ctor(1, 1, 0);
} else {
 x_906 = x_881;
 lean_ctor_set_tag(x_906, 1);
}
lean_ctor_set(x_906, 0, x_904);
if (lean_is_scalar(x_845)) {
 x_907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_907 = x_845;
}
lean_ctor_set(x_907, 0, x_843);
lean_ctor_set(x_907, 1, x_844);
x_908 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_908, 0, x_833);
lean_ctor_set(x_908, 1, x_907);
lean_ctor_set(x_2, 1, x_908);
lean_ctor_set(x_2, 0, x_906);
if (lean_is_scalar(x_905)) {
 x_909 = lean_alloc_ctor(0, 1, 0);
} else {
 x_909 = x_905;
}
lean_ctor_set(x_909, 0, x_2);
return x_909;
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; 
lean_dec(x_881);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec_ref(x_833);
lean_free_object(x_2);
x_910 = lean_ctor_get(x_903, 0);
lean_inc(x_910);
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 x_911 = x_903;
} else {
 lean_dec_ref(x_903);
 x_911 = lean_box(0);
}
if (lean_is_scalar(x_911)) {
 x_912 = lean_alloc_ctor(1, 1, 0);
} else {
 x_912 = x_911;
}
lean_ctor_set(x_912, 0, x_910);
return x_912;
}
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; 
lean_dec(x_843);
lean_inc(x_877);
x_913 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_913, 0, x_877);
x_914 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_914, 0, x_913);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_915 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_858, x_914, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
lean_dec_ref(x_915);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; 
lean_dec(x_1);
lean_inc(x_877);
x_917 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_877, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_917) == 0)
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 x_918 = x_917;
} else {
 lean_dec_ref(x_917);
 x_918 = lean_box(0);
}
if (lean_is_scalar(x_881)) {
 x_919 = lean_alloc_ctor(1, 1, 0);
} else {
 x_919 = x_881;
 lean_ctor_set_tag(x_919, 1);
}
lean_ctor_set(x_919, 0, x_916);
if (lean_is_scalar(x_845)) {
 x_920 = lean_alloc_ctor(0, 2, 0);
} else {
 x_920 = x_845;
}
lean_ctor_set(x_920, 0, x_877);
lean_ctor_set(x_920, 1, x_844);
x_921 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_921, 0, x_833);
lean_ctor_set(x_921, 1, x_920);
lean_ctor_set(x_2, 1, x_921);
lean_ctor_set(x_2, 0, x_919);
if (lean_is_scalar(x_918)) {
 x_922 = lean_alloc_ctor(0, 1, 0);
} else {
 x_922 = x_918;
}
lean_ctor_set(x_922, 0, x_2);
return x_922;
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_881);
lean_dec(x_877);
lean_dec(x_845);
lean_dec(x_844);
lean_dec_ref(x_833);
lean_free_object(x_2);
x_923 = lean_ctor_get(x_917, 0);
lean_inc(x_923);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 x_924 = x_917;
} else {
 lean_dec_ref(x_917);
 x_924 = lean_box(0);
}
if (lean_is_scalar(x_924)) {
 x_925 = lean_alloc_ctor(1, 1, 0);
} else {
 x_925 = x_924;
}
lean_ctor_set(x_925, 0, x_923);
return x_925;
}
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_881);
lean_inc(x_847);
lean_dec(x_844);
lean_dec_ref(x_833);
x_926 = lean_ctor_get(x_916, 0);
lean_inc(x_926);
lean_dec_ref(x_916);
if (lean_is_scalar(x_845)) {
 x_927 = lean_alloc_ctor(0, 2, 0);
} else {
 x_927 = x_845;
}
lean_ctor_set(x_927, 0, x_877);
lean_ctor_set(x_927, 1, x_926);
x_928 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_928, 0, x_847);
lean_ctor_set(x_928, 1, x_927);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_928);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
}
else
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; 
lean_dec(x_881);
lean_dec(x_877);
lean_dec(x_845);
lean_dec(x_844);
lean_dec_ref(x_833);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_930 = lean_ctor_get(x_915, 0);
lean_inc(x_930);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 x_931 = x_915;
} else {
 lean_dec_ref(x_915);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(1, 1, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_930);
return x_932;
}
}
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; 
lean_dec(x_881);
lean_dec(x_877);
lean_dec(x_858);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec_ref(x_833);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_933 = lean_ctor_get(x_884, 0);
lean_inc(x_933);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 x_934 = x_884;
} else {
 lean_dec_ref(x_884);
 x_934 = lean_box(0);
}
if (lean_is_scalar(x_934)) {
 x_935 = lean_alloc_ctor(1, 1, 0);
} else {
 x_935 = x_934;
}
lean_ctor_set(x_935, 0, x_933);
return x_935;
}
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_877);
lean_dec(x_858);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec_ref(x_833);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_936 = lean_ctor_get(x_878, 0);
lean_inc(x_936);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 x_937 = x_878;
} else {
 lean_dec_ref(x_878);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(1, 1, 0);
} else {
 x_938 = x_937;
}
lean_ctor_set(x_938, 0, x_936);
return x_938;
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_858);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec_ref(x_833);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_939 = lean_ctor_get(x_876, 0);
lean_inc(x_939);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 x_940 = x_876;
} else {
 lean_dec_ref(x_876);
 x_940 = lean_box(0);
}
if (lean_is_scalar(x_940)) {
 x_941 = lean_alloc_ctor(1, 1, 0);
} else {
 x_941 = x_940;
}
lean_ctor_set(x_941, 0, x_939);
return x_941;
}
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_942 = lean_ctor_get(x_854, 0);
lean_inc(x_942);
x_943 = lean_ctor_get(x_854, 1);
lean_inc(x_943);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_944 = x_854;
} else {
 lean_dec_ref(x_854);
 x_944 = lean_box(0);
}
x_945 = lean_st_ref_take(x_3);
x_946 = lean_ctor_get(x_945, 1);
lean_inc_ref(x_946);
x_947 = lean_ctor_get(x_945, 2);
lean_inc(x_947);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 lean_ctor_release(x_945, 2);
 lean_ctor_release(x_945, 3);
 x_948 = x_945;
} else {
 lean_dec_ref(x_945);
 x_948 = lean_box(0);
}
lean_inc(x_856);
if (lean_is_scalar(x_857)) {
 x_949 = lean_alloc_ctor(0, 6, 0);
} else {
 x_949 = x_857;
}
lean_ctor_set(x_949, 0, x_852);
lean_ctor_set(x_949, 1, x_849);
lean_ctor_set(x_949, 2, x_853);
lean_ctor_set(x_949, 3, x_943);
lean_ctor_set(x_949, 4, x_855);
lean_ctor_set(x_949, 5, x_856);
lean_inc(x_847);
if (lean_is_scalar(x_944)) {
 x_950 = lean_alloc_ctor(1, 2, 0);
} else {
 x_950 = x_944;
}
lean_ctor_set(x_950, 0, x_949);
lean_ctor_set(x_950, 1, x_847);
if (lean_is_scalar(x_948)) {
 x_951 = lean_alloc_ctor(0, 4, 0);
} else {
 x_951 = x_948;
}
lean_ctor_set(x_951, 0, x_942);
lean_ctor_set(x_951, 1, x_946);
lean_ctor_set(x_951, 2, x_947);
lean_ctor_set(x_951, 3, x_950);
x_952 = lean_st_ref_set(x_3, x_951);
lean_dec(x_3);
if (lean_is_scalar(x_851)) {
 x_953 = lean_alloc_ctor(1, 1, 0);
} else {
 x_953 = x_851;
 lean_ctor_set_tag(x_953, 1);
}
lean_ctor_set(x_953, 0, x_856);
x_954 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_954, 0, x_953);
if (lean_is_scalar(x_845)) {
 x_955 = lean_alloc_ctor(0, 2, 0);
} else {
 x_955 = x_845;
}
lean_ctor_set(x_955, 0, x_843);
lean_ctor_set(x_955, 1, x_844);
x_956 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_956, 0, x_833);
lean_ctor_set(x_956, 1, x_955);
lean_ctor_set(x_2, 1, x_956);
lean_ctor_set(x_2, 0, x_954);
if (lean_is_scalar(x_863)) {
 x_957 = lean_alloc_ctor(0, 1, 0);
} else {
 x_957 = x_863;
}
lean_ctor_set(x_957, 0, x_2);
return x_957;
}
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
lean_dec(x_863);
lean_inc(x_858);
lean_dec(x_857);
lean_dec(x_856);
lean_dec_ref(x_855);
lean_dec(x_854);
lean_dec_ref(x_853);
lean_dec(x_852);
lean_dec(x_851);
lean_dec_ref(x_849);
lean_inc(x_847);
lean_dec_ref(x_833);
x_958 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
lean_dec_ref(x_958);
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
lean_dec(x_959);
lean_inc(x_843);
x_961 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_961, 0, x_858);
lean_closure_set(x_961, 1, x_843);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_962 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_960, x_961, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_962) == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_963 = lean_ctor_get(x_962, 0);
lean_inc(x_963);
lean_dec_ref(x_962);
x_964 = lean_ctor_get(x_963, 1);
lean_inc(x_964);
lean_dec(x_963);
x_965 = lean_st_ref_take(x_3);
x_966 = lean_ctor_get(x_965, 1);
lean_inc_ref(x_966);
x_967 = lean_ctor_get(x_965, 2);
lean_inc(x_967);
x_968 = lean_ctor_get(x_965, 3);
lean_inc(x_968);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 lean_ctor_release(x_965, 2);
 lean_ctor_release(x_965, 3);
 x_969 = x_965;
} else {
 lean_dec_ref(x_965);
 x_969 = lean_box(0);
}
if (lean_is_scalar(x_969)) {
 x_970 = lean_alloc_ctor(0, 4, 0);
} else {
 x_970 = x_969;
}
lean_ctor_set(x_970, 0, x_964);
lean_ctor_set(x_970, 1, x_966);
lean_ctor_set(x_970, 2, x_967);
lean_ctor_set(x_970, 3, x_968);
x_971 = lean_st_ref_set(x_3, x_970);
if (lean_is_scalar(x_845)) {
 x_972 = lean_alloc_ctor(0, 2, 0);
} else {
 x_972 = x_845;
}
lean_ctor_set(x_972, 0, x_843);
lean_ctor_set(x_972, 1, x_844);
x_973 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_973, 0, x_847);
lean_ctor_set(x_973, 1, x_972);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_973);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; 
lean_dec(x_847);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_975 = lean_ctor_get(x_962, 0);
lean_inc(x_975);
if (lean_is_exclusive(x_962)) {
 lean_ctor_release(x_962, 0);
 x_976 = x_962;
} else {
 lean_dec_ref(x_962);
 x_976 = lean_box(0);
}
if (lean_is_scalar(x_976)) {
 x_977 = lean_alloc_ctor(1, 1, 0);
} else {
 x_977 = x_976;
}
lean_ctor_set(x_977, 0, x_975);
return x_977;
}
}
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; 
lean_dec(x_857);
lean_dec(x_856);
lean_dec_ref(x_855);
lean_dec(x_854);
lean_dec_ref(x_853);
lean_dec(x_852);
lean_dec(x_851);
lean_dec_ref(x_849);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec_ref(x_833);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_978 = lean_ctor_get(x_861, 0);
lean_inc(x_978);
if (lean_is_exclusive(x_861)) {
 lean_ctor_release(x_861, 0);
 x_979 = x_861;
} else {
 lean_dec_ref(x_861);
 x_979 = lean_box(0);
}
if (lean_is_scalar(x_979)) {
 x_980 = lean_alloc_ctor(1, 1, 0);
} else {
 x_980 = x_979;
}
lean_ctor_set(x_980, 0, x_978);
return x_980;
}
}
}
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_981 = lean_ctor_get(x_2, 1);
lean_inc(x_981);
lean_dec(x_2);
x_982 = lean_ctor_get(x_981, 1);
lean_inc(x_982);
x_983 = lean_ctor_get(x_981, 0);
lean_inc(x_983);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 lean_ctor_release(x_981, 1);
 x_984 = x_981;
} else {
 lean_dec_ref(x_981);
 x_984 = lean_box(0);
}
if (lean_obj_tag(x_983) == 0)
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_985 = lean_ctor_get(x_982, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_982, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_982)) {
 lean_ctor_release(x_982, 0);
 lean_ctor_release(x_982, 1);
 x_987 = x_982;
} else {
 lean_dec_ref(x_982);
 x_987 = lean_box(0);
}
x_988 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_3);
lean_dec(x_3);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 x_989 = x_988;
} else {
 lean_dec_ref(x_988);
 x_989 = lean_box(0);
}
x_990 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
if (lean_is_scalar(x_987)) {
 x_991 = lean_alloc_ctor(0, 2, 0);
} else {
 x_991 = x_987;
}
lean_ctor_set(x_991, 0, x_985);
lean_ctor_set(x_991, 1, x_986);
if (lean_is_scalar(x_984)) {
 x_992 = lean_alloc_ctor(0, 2, 0);
} else {
 x_992 = x_984;
}
lean_ctor_set(x_992, 0, x_983);
lean_ctor_set(x_992, 1, x_991);
x_993 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_993, 0, x_990);
lean_ctor_set(x_993, 1, x_992);
if (lean_is_scalar(x_989)) {
 x_994 = lean_alloc_ctor(0, 1, 0);
} else {
 x_994 = x_989;
}
lean_ctor_set(x_994, 0, x_993);
return x_994;
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_995 = lean_ctor_get(x_982, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_982, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_982)) {
 lean_ctor_release(x_982, 0);
 lean_ctor_release(x_982, 1);
 x_997 = x_982;
} else {
 lean_dec_ref(x_982);
 x_997 = lean_box(0);
}
x_998 = lean_ctor_get(x_983, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_983, 1);
x_1000 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_1001 = lean_ctor_get(x_998, 1);
lean_inc_ref(x_1001);
x_1002 = lean_ctor_get(x_1000, 0);
lean_inc(x_1002);
if (lean_is_exclusive(x_1000)) {
 lean_ctor_release(x_1000, 0);
 x_1003 = x_1000;
} else {
 lean_dec_ref(x_1000);
 x_1003 = lean_box(0);
}
x_1004 = lean_ctor_get(x_998, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_998, 2);
lean_inc_ref(x_1005);
x_1006 = lean_ctor_get(x_998, 3);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_998, 4);
lean_inc_ref(x_1007);
x_1008 = lean_ctor_get(x_998, 5);
lean_inc(x_1008);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 lean_ctor_release(x_998, 2);
 lean_ctor_release(x_998, 3);
 lean_ctor_release(x_998, 4);
 lean_ctor_release(x_998, 5);
 x_1009 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1009 = lean_box(0);
}
x_1010 = lean_ctor_get(x_1001, 0);
x_1011 = lean_ctor_get(x_1002, 0);
lean_inc(x_1011);
lean_dec(x_1002);
lean_inc(x_1010);
x_1012 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_1012, 0, x_1010);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1013 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1011, x_1012, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1013) == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; uint8_t x_1027; 
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 x_1015 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1015 = lean_box(0);
}
x_1016 = lean_ctor_get(x_1014, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1014, 1);
lean_inc(x_1017);
lean_dec(x_1014);
x_1018 = lean_st_ref_take(x_3);
x_1019 = lean_ctor_get(x_1018, 1);
lean_inc_ref(x_1019);
x_1020 = lean_ctor_get(x_1018, 2);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1018, 3);
lean_inc(x_1021);
if (lean_is_exclusive(x_1018)) {
 lean_ctor_release(x_1018, 0);
 lean_ctor_release(x_1018, 1);
 lean_ctor_release(x_1018, 2);
 lean_ctor_release(x_1018, 3);
 x_1022 = x_1018;
} else {
 lean_dec_ref(x_1018);
 x_1022 = lean_box(0);
}
if (lean_is_scalar(x_1022)) {
 x_1023 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1023 = x_1022;
}
lean_ctor_set(x_1023, 0, x_1017);
lean_ctor_set(x_1023, 1, x_1019);
lean_ctor_set(x_1023, 2, x_1020);
lean_ctor_set(x_1023, 3, x_1021);
x_1024 = lean_st_ref_set(x_3, x_1023);
x_1025 = lean_ctor_get(x_1016, 1);
lean_inc_ref(x_1025);
lean_dec(x_1016);
x_1026 = lean_local_ctx_num_indices(x_1025);
x_1027 = lean_nat_dec_lt(x_996, x_1026);
lean_dec(x_1026);
if (x_1027 == 0)
{
if (lean_obj_tag(x_1006) == 0)
{
lean_object* x_1028; 
lean_dec(x_1015);
lean_inc(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec_ref(x_1007);
lean_dec(x_1004);
lean_dec(x_1003);
lean_dec_ref(x_1001);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1028 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_1005, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1028) == 0)
{
lean_object* x_1029; lean_object* x_1030; 
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
lean_dec_ref(x_1028);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1029);
lean_inc(x_1010);
x_1030 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_1010, x_1029, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1030) == 0)
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
lean_dec_ref(x_1030);
x_1031 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 x_1033 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1033 = lean_box(0);
}
x_1034 = lean_ctor_get(x_1032, 0);
lean_inc(x_1034);
lean_dec(x_1032);
lean_inc(x_1010);
x_1035 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_1035, 0, x_1010);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1036 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1034, x_1035, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; uint8_t x_1047; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
lean_dec_ref(x_1036);
x_1038 = lean_ctor_get(x_1037, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1037, 1);
lean_inc(x_1039);
lean_dec(x_1037);
x_1040 = lean_st_ref_take(x_3);
x_1041 = lean_ctor_get(x_1040, 1);
lean_inc_ref(x_1041);
x_1042 = lean_ctor_get(x_1040, 2);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1040, 3);
lean_inc(x_1043);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 lean_ctor_release(x_1040, 2);
 lean_ctor_release(x_1040, 3);
 x_1044 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1044 = lean_box(0);
}
if (lean_is_scalar(x_1044)) {
 x_1045 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1045 = x_1044;
}
lean_ctor_set(x_1045, 0, x_1039);
lean_ctor_set(x_1045, 1, x_1041);
lean_ctor_set(x_1045, 2, x_1042);
lean_ctor_set(x_1045, 3, x_1043);
x_1046 = lean_st_ref_set(x_3, x_1045);
x_1047 = lean_unbox(x_1038);
lean_dec(x_1038);
if (x_1047 == 0)
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_1029);
lean_dec(x_1010);
lean_dec(x_1);
x_1048 = lean_st_ref_take(x_3);
x_1049 = lean_ctor_get(x_1048, 0);
lean_inc_ref(x_1049);
x_1050 = lean_ctor_get(x_1048, 1);
lean_inc_ref(x_1050);
x_1051 = lean_ctor_get(x_1048, 2);
lean_inc(x_1051);
if (lean_is_exclusive(x_1048)) {
 lean_ctor_release(x_1048, 0);
 lean_ctor_release(x_1048, 1);
 lean_ctor_release(x_1048, 2);
 lean_ctor_release(x_1048, 3);
 x_1052 = x_1048;
} else {
 lean_dec_ref(x_1048);
 x_1052 = lean_box(0);
}
lean_inc(x_999);
if (lean_is_scalar(x_1052)) {
 x_1053 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1053 = x_1052;
}
lean_ctor_set(x_1053, 0, x_1049);
lean_ctor_set(x_1053, 1, x_1050);
lean_ctor_set(x_1053, 2, x_1051);
lean_ctor_set(x_1053, 3, x_999);
x_1054 = lean_st_ref_set(x_3, x_1053);
x_1055 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1055) == 0)
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
x_1056 = lean_ctor_get(x_1055, 0);
lean_inc(x_1056);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 x_1057 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1057 = lean_box(0);
}
if (lean_is_scalar(x_1033)) {
 x_1058 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1058 = x_1033;
 lean_ctor_set_tag(x_1058, 1);
}
lean_ctor_set(x_1058, 0, x_1056);
if (lean_is_scalar(x_997)) {
 x_1059 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1059 = x_997;
}
lean_ctor_set(x_1059, 0, x_995);
lean_ctor_set(x_1059, 1, x_996);
if (lean_is_scalar(x_984)) {
 x_1060 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1060 = x_984;
}
lean_ctor_set(x_1060, 0, x_983);
lean_ctor_set(x_1060, 1, x_1059);
x_1061 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1061, 0, x_1058);
lean_ctor_set(x_1061, 1, x_1060);
if (lean_is_scalar(x_1057)) {
 x_1062 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1062 = x_1057;
}
lean_ctor_set(x_1062, 0, x_1061);
return x_1062;
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_1033);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec_ref(x_983);
x_1063 = lean_ctor_get(x_1055, 0);
lean_inc(x_1063);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 x_1064 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1064 = lean_box(0);
}
if (lean_is_scalar(x_1064)) {
 x_1065 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1065 = x_1064;
}
lean_ctor_set(x_1065, 0, x_1063);
return x_1065;
}
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_995);
lean_inc(x_1029);
x_1066 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_1066, 0, x_1029);
x_1067 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_1067, 0, x_1066);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1068 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1010, x_1067, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; 
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
lean_dec_ref(x_1068);
if (lean_obj_tag(x_1069) == 0)
{
lean_object* x_1070; 
lean_dec(x_1);
lean_inc(x_1029);
x_1070 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_1029, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 x_1071 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1071 = lean_box(0);
}
if (lean_is_scalar(x_1033)) {
 x_1072 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1072 = x_1033;
 lean_ctor_set_tag(x_1072, 1);
}
lean_ctor_set(x_1072, 0, x_1069);
if (lean_is_scalar(x_997)) {
 x_1073 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1073 = x_997;
}
lean_ctor_set(x_1073, 0, x_1029);
lean_ctor_set(x_1073, 1, x_996);
if (lean_is_scalar(x_984)) {
 x_1074 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1074 = x_984;
}
lean_ctor_set(x_1074, 0, x_983);
lean_ctor_set(x_1074, 1, x_1073);
x_1075 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1075, 0, x_1072);
lean_ctor_set(x_1075, 1, x_1074);
if (lean_is_scalar(x_1071)) {
 x_1076 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1076 = x_1071;
}
lean_ctor_set(x_1076, 0, x_1075);
return x_1076;
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
lean_dec(x_1033);
lean_dec(x_1029);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_984);
lean_dec_ref(x_983);
x_1077 = lean_ctor_get(x_1070, 0);
lean_inc(x_1077);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 x_1078 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1078 = lean_box(0);
}
if (lean_is_scalar(x_1078)) {
 x_1079 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1079 = x_1078;
}
lean_ctor_set(x_1079, 0, x_1077);
return x_1079;
}
}
else
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
lean_dec(x_1033);
lean_inc(x_999);
lean_dec(x_996);
lean_dec_ref(x_983);
x_1080 = lean_ctor_get(x_1069, 0);
lean_inc(x_1080);
lean_dec_ref(x_1069);
if (lean_is_scalar(x_997)) {
 x_1081 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1081 = x_997;
}
lean_ctor_set(x_1081, 0, x_1029);
lean_ctor_set(x_1081, 1, x_1080);
if (lean_is_scalar(x_984)) {
 x_1082 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1082 = x_984;
}
lean_ctor_set(x_1082, 0, x_999);
lean_ctor_set(x_1082, 1, x_1081);
lean_inc(x_1);
x_1083 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1083, 0, x_1);
lean_ctor_set(x_1083, 1, x_1082);
x_2 = x_1083;
goto _start;
}
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_1033);
lean_dec(x_1029);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_984);
lean_dec_ref(x_983);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1085 = lean_ctor_get(x_1068, 0);
lean_inc(x_1085);
if (lean_is_exclusive(x_1068)) {
 lean_ctor_release(x_1068, 0);
 x_1086 = x_1068;
} else {
 lean_dec_ref(x_1068);
 x_1086 = lean_box(0);
}
if (lean_is_scalar(x_1086)) {
 x_1087 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1087 = x_1086;
}
lean_ctor_set(x_1087, 0, x_1085);
return x_1087;
}
}
}
else
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
lean_dec(x_1033);
lean_dec(x_1029);
lean_dec(x_1010);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec_ref(x_983);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1088 = lean_ctor_get(x_1036, 0);
lean_inc(x_1088);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 x_1089 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1089 = lean_box(0);
}
if (lean_is_scalar(x_1089)) {
 x_1090 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1090 = x_1089;
}
lean_ctor_set(x_1090, 0, x_1088);
return x_1090;
}
}
else
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
lean_dec(x_1029);
lean_dec(x_1010);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec_ref(x_983);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1091 = lean_ctor_get(x_1030, 0);
lean_inc(x_1091);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 x_1092 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1092 = lean_box(0);
}
if (lean_is_scalar(x_1092)) {
 x_1093 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1093 = x_1092;
}
lean_ctor_set(x_1093, 0, x_1091);
return x_1093;
}
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
lean_dec(x_1010);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec_ref(x_983);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1094 = lean_ctor_get(x_1028, 0);
lean_inc(x_1094);
if (lean_is_exclusive(x_1028)) {
 lean_ctor_release(x_1028, 0);
 x_1095 = x_1028;
} else {
 lean_dec_ref(x_1028);
 x_1095 = lean_box(0);
}
if (lean_is_scalar(x_1095)) {
 x_1096 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1096 = x_1095;
}
lean_ctor_set(x_1096, 0, x_1094);
return x_1096;
}
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1097 = lean_ctor_get(x_1006, 0);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1006, 1);
lean_inc(x_1098);
if (lean_is_exclusive(x_1006)) {
 lean_ctor_release(x_1006, 0);
 lean_ctor_release(x_1006, 1);
 x_1099 = x_1006;
} else {
 lean_dec_ref(x_1006);
 x_1099 = lean_box(0);
}
x_1100 = lean_st_ref_take(x_3);
x_1101 = lean_ctor_get(x_1100, 1);
lean_inc_ref(x_1101);
x_1102 = lean_ctor_get(x_1100, 2);
lean_inc(x_1102);
if (lean_is_exclusive(x_1100)) {
 lean_ctor_release(x_1100, 0);
 lean_ctor_release(x_1100, 1);
 lean_ctor_release(x_1100, 2);
 lean_ctor_release(x_1100, 3);
 x_1103 = x_1100;
} else {
 lean_dec_ref(x_1100);
 x_1103 = lean_box(0);
}
lean_inc(x_1008);
if (lean_is_scalar(x_1009)) {
 x_1104 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1104 = x_1009;
}
lean_ctor_set(x_1104, 0, x_1004);
lean_ctor_set(x_1104, 1, x_1001);
lean_ctor_set(x_1104, 2, x_1005);
lean_ctor_set(x_1104, 3, x_1098);
lean_ctor_set(x_1104, 4, x_1007);
lean_ctor_set(x_1104, 5, x_1008);
lean_inc(x_999);
if (lean_is_scalar(x_1099)) {
 x_1105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1105 = x_1099;
}
lean_ctor_set(x_1105, 0, x_1104);
lean_ctor_set(x_1105, 1, x_999);
if (lean_is_scalar(x_1103)) {
 x_1106 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1106 = x_1103;
}
lean_ctor_set(x_1106, 0, x_1097);
lean_ctor_set(x_1106, 1, x_1101);
lean_ctor_set(x_1106, 2, x_1102);
lean_ctor_set(x_1106, 3, x_1105);
x_1107 = lean_st_ref_set(x_3, x_1106);
lean_dec(x_3);
if (lean_is_scalar(x_1003)) {
 x_1108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1108 = x_1003;
 lean_ctor_set_tag(x_1108, 1);
}
lean_ctor_set(x_1108, 0, x_1008);
x_1109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1109, 0, x_1108);
if (lean_is_scalar(x_997)) {
 x_1110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1110 = x_997;
}
lean_ctor_set(x_1110, 0, x_995);
lean_ctor_set(x_1110, 1, x_996);
if (lean_is_scalar(x_984)) {
 x_1111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1111 = x_984;
}
lean_ctor_set(x_1111, 0, x_983);
lean_ctor_set(x_1111, 1, x_1110);
x_1112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1112, 0, x_1109);
lean_ctor_set(x_1112, 1, x_1111);
if (lean_is_scalar(x_1015)) {
 x_1113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1113 = x_1015;
}
lean_ctor_set(x_1113, 0, x_1112);
return x_1113;
}
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
lean_dec(x_1015);
lean_inc(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec_ref(x_1007);
lean_dec(x_1006);
lean_dec_ref(x_1005);
lean_dec(x_1004);
lean_dec(x_1003);
lean_dec_ref(x_1001);
lean_inc(x_999);
lean_dec_ref(x_983);
x_1114 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_1115 = lean_ctor_get(x_1114, 0);
lean_inc(x_1115);
lean_dec_ref(x_1114);
x_1116 = lean_ctor_get(x_1115, 0);
lean_inc(x_1116);
lean_dec(x_1115);
lean_inc(x_995);
x_1117 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_1117, 0, x_1010);
lean_closure_set(x_1117, 1, x_995);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1118 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1116, x_1117, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1118) == 0)
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1119 = lean_ctor_get(x_1118, 0);
lean_inc(x_1119);
lean_dec_ref(x_1118);
x_1120 = lean_ctor_get(x_1119, 1);
lean_inc(x_1120);
lean_dec(x_1119);
x_1121 = lean_st_ref_take(x_3);
x_1122 = lean_ctor_get(x_1121, 1);
lean_inc_ref(x_1122);
x_1123 = lean_ctor_get(x_1121, 2);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1121, 3);
lean_inc(x_1124);
if (lean_is_exclusive(x_1121)) {
 lean_ctor_release(x_1121, 0);
 lean_ctor_release(x_1121, 1);
 lean_ctor_release(x_1121, 2);
 lean_ctor_release(x_1121, 3);
 x_1125 = x_1121;
} else {
 lean_dec_ref(x_1121);
 x_1125 = lean_box(0);
}
if (lean_is_scalar(x_1125)) {
 x_1126 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1126 = x_1125;
}
lean_ctor_set(x_1126, 0, x_1120);
lean_ctor_set(x_1126, 1, x_1122);
lean_ctor_set(x_1126, 2, x_1123);
lean_ctor_set(x_1126, 3, x_1124);
x_1127 = lean_st_ref_set(x_3, x_1126);
if (lean_is_scalar(x_997)) {
 x_1128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1128 = x_997;
}
lean_ctor_set(x_1128, 0, x_995);
lean_ctor_set(x_1128, 1, x_996);
if (lean_is_scalar(x_984)) {
 x_1129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1129 = x_984;
}
lean_ctor_set(x_1129, 0, x_999);
lean_ctor_set(x_1129, 1, x_1128);
lean_inc(x_1);
x_1130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1130, 0, x_1);
lean_ctor_set(x_1130, 1, x_1129);
x_2 = x_1130;
goto _start;
}
else
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; 
lean_dec(x_999);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1132 = lean_ctor_get(x_1118, 0);
lean_inc(x_1132);
if (lean_is_exclusive(x_1118)) {
 lean_ctor_release(x_1118, 0);
 x_1133 = x_1118;
} else {
 lean_dec_ref(x_1118);
 x_1133 = lean_box(0);
}
if (lean_is_scalar(x_1133)) {
 x_1134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1134 = x_1133;
}
lean_ctor_set(x_1134, 0, x_1132);
return x_1134;
}
}
}
else
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec_ref(x_1007);
lean_dec(x_1006);
lean_dec_ref(x_1005);
lean_dec(x_1004);
lean_dec(x_1003);
lean_dec_ref(x_1001);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec_ref(x_983);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1135 = lean_ctor_get(x_1013, 0);
lean_inc(x_1135);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 x_1136 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1136 = lean_box(0);
}
if (lean_is_scalar(x_1136)) {
 x_1137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1137 = x_1136;
}
lean_ctor_set(x_1137, 0, x_1135);
return x_1137;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_3);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
lean_ctor_set(x_2, 0, x_22);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_23 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
lean_ctor_set(x_2, 0, x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_2);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_3);
lean_dec(x_3);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_28 = x_27;
} else {
 lean_dec_ref(x_27);
 x_28 = lean_box(0);
}
x_29 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_13, 1, x_30);
lean_ctor_set(x_2, 0, x_29);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_2);
return x_31;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_13, 1);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_16, 1);
x_38 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_39 = lean_ctor_get(x_36, 1);
lean_inc_ref(x_39);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 2);
x_45 = lean_ctor_get(x_36, 3);
x_46 = lean_ctor_get(x_36, 4);
x_47 = lean_ctor_get(x_36, 5);
x_48 = lean_ctor_get(x_36, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
lean_inc(x_49);
x_51 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_51, 0, x_49);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_52 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_50, x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_st_ref_take(x_3);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_56);
x_60 = lean_st_ref_set(x_3, x_57);
x_61 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_61);
lean_dec(x_55);
x_62 = lean_local_ctx_num_indices(x_61);
x_63 = lean_nat_dec_lt(x_35, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_64; 
lean_free_object(x_52);
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_64 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_65);
lean_inc(x_49);
x_66 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_49, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
lean_dec_ref(x_66);
x_67 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
lean_inc(x_49);
x_71 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_71, 0, x_49);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_72 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_70, x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_take(x_3);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_75);
x_79 = lean_st_ref_set(x_3, x_76);
x_80 = lean_unbox(x_74);
lean_dec(x_74);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
lean_dec(x_65);
lean_dec(x_49);
lean_dec(x_1);
x_81 = lean_st_ref_take(x_3);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 3);
lean_dec(x_83);
lean_inc(x_37);
lean_ctor_set(x_81, 3, x_37);
x_84 = lean_st_ref_set(x_3, x_81);
x_85 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_87);
lean_ctor_set(x_2, 0, x_67);
lean_ctor_set(x_85, 0, x_2);
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec(x_85);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_88);
lean_ctor_set(x_2, 0, x_67);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_2);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_free_object(x_67);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_90 = !lean_is_exclusive(x_85);
if (x_90 == 0)
{
return x_85;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_81, 0);
x_94 = lean_ctor_get(x_81, 1);
x_95 = lean_ctor_get(x_81, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_81);
lean_inc(x_37);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_37);
x_97 = lean_st_ref_set(x_3, x_96);
x_98 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_99);
lean_ctor_set(x_2, 0, x_67);
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_2);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_67);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_102 = lean_ctor_get(x_98, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_103 = x_98;
} else {
 lean_dec_ref(x_98);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_34);
lean_inc(x_65);
x_105 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_105, 0, x_65);
x_106 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_106, 0, x_105);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_107 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_49, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
lean_dec(x_1);
lean_inc(x_65);
x_109 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_109, 0);
lean_dec(x_111);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_108);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_2, 0, x_67);
lean_ctor_set(x_109, 0, x_2);
return x_109;
}
else
{
lean_object* x_112; 
lean_dec(x_109);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_108);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_2, 0, x_67);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_2);
return x_112;
}
}
else
{
uint8_t x_113; 
lean_free_object(x_67);
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_113 = !lean_is_exclusive(x_109);
if (x_113 == 0)
{
return x_109;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_free_object(x_67);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_116 = lean_ctor_get(x_108, 0);
lean_inc(x_116);
lean_dec_ref(x_108);
lean_ctor_set(x_32, 1, x_116);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_117 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_free_object(x_67);
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_107);
if (x_118 == 0)
{
return x_107;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_107, 0);
lean_inc(x_119);
lean_dec(x_107);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_76, 1);
x_122 = lean_ctor_get(x_76, 2);
x_123 = lean_ctor_get(x_76, 3);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_76);
x_124 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_124, 0, x_75);
lean_ctor_set(x_124, 1, x_121);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_123);
x_125 = lean_st_ref_set(x_3, x_124);
x_126 = lean_unbox(x_74);
lean_dec(x_74);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_65);
lean_dec(x_49);
lean_dec(x_1);
x_127 = lean_st_ref_take(x_3);
x_128 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_127, 2);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 4, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_129);
lean_ctor_set(x_132, 2, x_130);
lean_ctor_set(x_132, 3, x_37);
x_133 = lean_st_ref_set(x_3, x_132);
x_134 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_135);
lean_ctor_set(x_2, 0, x_67);
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 1, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_2);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_free_object(x_67);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_138 = lean_ctor_get(x_134, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_139 = x_134;
} else {
 lean_dec_ref(x_134);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_34);
lean_inc(x_65);
x_141 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_141, 0, x_65);
x_142 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_142, 0, x_141);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_143 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_49, x_142, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec_ref(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
lean_dec(x_1);
lean_inc(x_65);
x_145 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; 
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_146 = x_145;
} else {
 lean_dec_ref(x_145);
 x_146 = lean_box(0);
}
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_144);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_2, 0, x_67);
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 1, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_2);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_free_object(x_67);
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_149 = x_145;
} else {
 lean_dec_ref(x_145);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_free_object(x_67);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_151 = lean_ctor_get(x_144, 0);
lean_inc(x_151);
lean_dec_ref(x_144);
lean_ctor_set(x_32, 1, x_151);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_152 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_free_object(x_67);
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = lean_ctor_get(x_143, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_154 = x_143;
} else {
 lean_dec_ref(x_143);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
}
}
}
else
{
uint8_t x_156; 
lean_free_object(x_67);
lean_dec(x_65);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_72);
if (x_156 == 0)
{
return x_72;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_72, 0);
lean_inc(x_157);
lean_dec(x_72);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_67, 0);
lean_inc(x_159);
lean_dec(x_67);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
lean_inc(x_49);
x_161 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_161, 0, x_49);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_162 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_160, x_161, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_st_ref_take(x_3);
x_167 = lean_ctor_get(x_166, 1);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_166, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 x_170 = x_166;
} else {
 lean_dec_ref(x_166);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 4, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_167);
lean_ctor_set(x_171, 2, x_168);
lean_ctor_set(x_171, 3, x_169);
x_172 = lean_st_ref_set(x_3, x_171);
x_173 = lean_unbox(x_164);
lean_dec(x_164);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_65);
lean_dec(x_49);
lean_dec(x_1);
x_174 = lean_st_ref_take(x_3);
x_175 = lean_ctor_get(x_174, 0);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_174, 2);
lean_inc(x_177);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 lean_ctor_release(x_174, 2);
 lean_ctor_release(x_174, 3);
 x_178 = x_174;
} else {
 lean_dec_ref(x_174);
 x_178 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 4, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_37);
x_180 = lean_st_ref_set(x_3, x_179);
x_181 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_2, 0, x_184);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 1, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_2);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_186 = lean_ctor_get(x_181, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_187 = x_181;
} else {
 lean_dec_ref(x_181);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_34);
lean_inc(x_65);
x_189 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_189, 0, x_65);
x_190 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_190, 0, x_189);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_191 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_49, x_190, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec_ref(x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
lean_dec(x_1);
lean_inc(x_65);
x_193 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_194 = x_193;
} else {
 lean_dec_ref(x_193);
 x_194 = lean_box(0);
}
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_2, 0, x_195);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 1, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_2);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_197 = lean_ctor_get(x_193, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_198 = x_193;
} else {
 lean_dec_ref(x_193);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 1, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_200 = lean_ctor_get(x_192, 0);
lean_inc(x_200);
lean_dec_ref(x_192);
lean_ctor_set(x_32, 1, x_200);
lean_ctor_set(x_32, 0, x_65);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_201 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_65);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_202 = lean_ctor_get(x_191, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 x_203 = x_191;
} else {
 lean_dec_ref(x_191);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_65);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_205 = lean_ctor_get(x_162, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_206 = x_162;
} else {
 lean_dec_ref(x_162);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_65);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_66);
if (x_208 == 0)
{
return x_66;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_66, 0);
lean_inc(x_209);
lean_dec(x_66);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_64);
if (x_211 == 0)
{
return x_64;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_64, 0);
lean_inc(x_212);
lean_dec(x_64);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_45);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_215 = lean_ctor_get(x_45, 0);
x_216 = lean_ctor_get(x_45, 1);
x_217 = lean_st_ref_take(x_3);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_217, 3);
lean_dec(x_219);
x_220 = lean_ctor_get(x_217, 0);
lean_dec(x_220);
lean_inc(x_47);
lean_ctor_set(x_36, 3, x_216);
lean_inc(x_37);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_217, 3, x_45);
lean_ctor_set(x_217, 0, x_215);
x_221 = lean_st_ref_set(x_3, x_217);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_38);
lean_ctor_set(x_2, 0, x_222);
lean_ctor_set(x_52, 0, x_2);
return x_52;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_217, 1);
x_224 = lean_ctor_get(x_217, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_217);
lean_inc(x_47);
lean_ctor_set(x_36, 3, x_216);
lean_inc(x_37);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 0, x_36);
x_225 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_225, 0, x_215);
lean_ctor_set(x_225, 1, x_223);
lean_ctor_set(x_225, 2, x_224);
lean_ctor_set(x_225, 3, x_45);
x_226 = lean_st_ref_set(x_3, x_225);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_38);
lean_ctor_set(x_2, 0, x_227);
lean_ctor_set(x_52, 0, x_2);
return x_52;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_228 = lean_ctor_get(x_45, 0);
x_229 = lean_ctor_get(x_45, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_45);
x_230 = lean_st_ref_take(x_3);
x_231 = lean_ctor_get(x_230, 1);
lean_inc_ref(x_231);
x_232 = lean_ctor_get(x_230, 2);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 lean_ctor_release(x_230, 2);
 lean_ctor_release(x_230, 3);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
lean_inc(x_47);
lean_ctor_set(x_36, 3, x_229);
lean_inc(x_37);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_36);
lean_ctor_set(x_234, 1, x_37);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(0, 4, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_228);
lean_ctor_set(x_235, 1, x_231);
lean_ctor_set(x_235, 2, x_232);
lean_ctor_set(x_235, 3, x_234);
x_236 = lean_st_ref_set(x_3, x_235);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_38);
lean_ctor_set(x_2, 0, x_237);
lean_ctor_set(x_52, 0, x_2);
return x_52;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_free_object(x_52);
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_37);
lean_dec_ref(x_16);
x_238 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec(x_239);
lean_inc(x_34);
x_241 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_241, 0, x_49);
lean_closure_set(x_241, 1, x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_242 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_240, x_241, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
lean_dec_ref(x_242);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_st_ref_take(x_3);
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_245, 0);
lean_dec(x_247);
lean_ctor_set(x_245, 0, x_244);
x_248 = lean_st_ref_set(x_3, x_245);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_249 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_250 = lean_ctor_get(x_245, 1);
x_251 = lean_ctor_get(x_245, 2);
x_252 = lean_ctor_get(x_245, 3);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_245);
x_253 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_253, 0, x_244);
lean_ctor_set(x_253, 1, x_250);
lean_ctor_set(x_253, 2, x_251);
lean_ctor_set(x_253, 3, x_252);
x_254 = lean_st_ref_set(x_3, x_253);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_255 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_255;
}
}
else
{
uint8_t x_256; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_242);
if (x_256 == 0)
{
return x_242;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_242, 0);
lean_inc(x_257);
lean_dec(x_242);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_259 = lean_ctor_get(x_57, 1);
x_260 = lean_ctor_get(x_57, 2);
x_261 = lean_ctor_get(x_57, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_57);
x_262 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_262, 0, x_56);
lean_ctor_set(x_262, 1, x_259);
lean_ctor_set(x_262, 2, x_260);
lean_ctor_set(x_262, 3, x_261);
x_263 = lean_st_ref_set(x_3, x_262);
x_264 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_264);
lean_dec(x_55);
x_265 = lean_local_ctx_num_indices(x_264);
x_266 = lean_nat_dec_lt(x_35, x_265);
lean_dec(x_265);
if (x_266 == 0)
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_267; 
lean_free_object(x_52);
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_267 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec_ref(x_267);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_268);
lean_inc(x_49);
x_269 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_49, x_268, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec_ref(x_269);
x_270 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
x_273 = lean_ctor_get(x_271, 0);
lean_inc(x_273);
lean_dec(x_271);
lean_inc(x_49);
x_274 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_274, 0, x_49);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_275 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_273, x_274, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_st_ref_take(x_3);
x_280 = lean_ctor_get(x_279, 1);
lean_inc_ref(x_280);
x_281 = lean_ctor_get(x_279, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_279, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 x_283 = x_279;
} else {
 lean_dec_ref(x_279);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 4, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_278);
lean_ctor_set(x_284, 1, x_280);
lean_ctor_set(x_284, 2, x_281);
lean_ctor_set(x_284, 3, x_282);
x_285 = lean_st_ref_set(x_3, x_284);
x_286 = lean_unbox(x_277);
lean_dec(x_277);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_268);
lean_dec(x_49);
lean_dec(x_1);
x_287 = lean_st_ref_take(x_3);
x_288 = lean_ctor_get(x_287, 0);
lean_inc_ref(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc_ref(x_289);
x_290 = lean_ctor_get(x_287, 2);
lean_inc(x_290);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 lean_ctor_release(x_287, 2);
 lean_ctor_release(x_287, 3);
 x_291 = x_287;
} else {
 lean_dec_ref(x_287);
 x_291 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 4, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_288);
lean_ctor_set(x_292, 1, x_289);
lean_ctor_set(x_292, 2, x_290);
lean_ctor_set(x_292, 3, x_37);
x_293 = lean_st_ref_set(x_3, x_292);
x_294 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_296 = x_294;
} else {
 lean_dec_ref(x_294);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_272;
 lean_ctor_set_tag(x_297, 1);
}
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_2, 0, x_297);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(0, 1, 0);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_2);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_272);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_299 = lean_ctor_get(x_294, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_300 = x_294;
} else {
 lean_dec_ref(x_294);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_34);
lean_inc(x_268);
x_302 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_302, 0, x_268);
x_303 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_303, 0, x_302);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_304 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_49, x_303, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec_ref(x_304);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; 
lean_dec(x_1);
lean_inc(x_268);
x_306 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_268, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_307 = x_306;
} else {
 lean_dec_ref(x_306);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_308 = lean_alloc_ctor(1, 1, 0);
} else {
 x_308 = x_272;
 lean_ctor_set_tag(x_308, 1);
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_32, 0, x_268);
lean_ctor_set(x_2, 0, x_308);
if (lean_is_scalar(x_307)) {
 x_309 = lean_alloc_ctor(0, 1, 0);
} else {
 x_309 = x_307;
}
lean_ctor_set(x_309, 0, x_2);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_272);
lean_dec(x_268);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_310 = lean_ctor_get(x_306, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_311 = x_306;
} else {
 lean_dec_ref(x_306);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 1, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_272);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_313 = lean_ctor_get(x_305, 0);
lean_inc(x_313);
lean_dec_ref(x_305);
lean_ctor_set(x_32, 1, x_313);
lean_ctor_set(x_32, 0, x_268);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_314 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_272);
lean_dec(x_268);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_315 = lean_ctor_get(x_304, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 x_316 = x_304;
} else {
 lean_dec_ref(x_304);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 1, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_315);
return x_317;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_272);
lean_dec(x_268);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_318 = lean_ctor_get(x_275, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_319 = x_275;
} else {
 lean_dec_ref(x_275);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 1, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_318);
return x_320;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_268);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_321 = lean_ctor_get(x_269, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_322 = x_269;
} else {
 lean_dec_ref(x_269);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_321);
return x_323;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_324 = lean_ctor_get(x_267, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_325 = x_267;
} else {
 lean_dec_ref(x_267);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 1, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_324);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_327 = lean_ctor_get(x_45, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_45, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_329 = x_45;
} else {
 lean_dec_ref(x_45);
 x_329 = lean_box(0);
}
x_330 = lean_st_ref_take(x_3);
x_331 = lean_ctor_get(x_330, 1);
lean_inc_ref(x_331);
x_332 = lean_ctor_get(x_330, 2);
lean_inc(x_332);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 x_333 = x_330;
} else {
 lean_dec_ref(x_330);
 x_333 = lean_box(0);
}
lean_inc(x_47);
lean_ctor_set(x_36, 3, x_328);
lean_inc(x_37);
if (lean_is_scalar(x_329)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_329;
}
lean_ctor_set(x_334, 0, x_36);
lean_ctor_set(x_334, 1, x_37);
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 4, 0);
} else {
 x_335 = x_333;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_331);
lean_ctor_set(x_335, 2, x_332);
lean_ctor_set(x_335, 3, x_334);
x_336 = lean_st_ref_set(x_3, x_335);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
x_337 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_337, 0, x_38);
lean_ctor_set(x_2, 0, x_337);
lean_ctor_set(x_52, 0, x_2);
return x_52;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_free_object(x_52);
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_37);
lean_dec_ref(x_16);
x_338 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
lean_dec(x_339);
lean_inc(x_34);
x_341 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_341, 0, x_49);
lean_closure_set(x_341, 1, x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_342 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_340, x_341, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec_ref(x_342);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
lean_dec(x_343);
x_345 = lean_st_ref_take(x_3);
x_346 = lean_ctor_get(x_345, 1);
lean_inc_ref(x_346);
x_347 = lean_ctor_get(x_345, 2);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 3);
lean_inc(x_348);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 x_349 = x_345;
} else {
 lean_dec_ref(x_345);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(0, 4, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_344);
lean_ctor_set(x_350, 1, x_346);
lean_ctor_set(x_350, 2, x_347);
lean_ctor_set(x_350, 3, x_348);
x_351 = lean_st_ref_set(x_3, x_350);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_352 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_353 = lean_ctor_get(x_342, 0);
lean_inc(x_353);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_354 = x_342;
} else {
 lean_dec_ref(x_342);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 1, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_353);
return x_355;
}
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_356 = lean_ctor_get(x_52, 0);
lean_inc(x_356);
lean_dec(x_52);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = lean_st_ref_take(x_3);
x_360 = lean_ctor_get(x_359, 1);
lean_inc_ref(x_360);
x_361 = lean_ctor_get(x_359, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_359, 3);
lean_inc(x_362);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 lean_ctor_release(x_359, 2);
 lean_ctor_release(x_359, 3);
 x_363 = x_359;
} else {
 lean_dec_ref(x_359);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(0, 4, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_358);
lean_ctor_set(x_364, 1, x_360);
lean_ctor_set(x_364, 2, x_361);
lean_ctor_set(x_364, 3, x_362);
x_365 = lean_st_ref_set(x_3, x_364);
x_366 = lean_ctor_get(x_357, 1);
lean_inc_ref(x_366);
lean_dec(x_357);
x_367 = lean_local_ctx_num_indices(x_366);
x_368 = lean_nat_dec_lt(x_35, x_367);
lean_dec(x_367);
if (x_368 == 0)
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_369; 
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_369 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
lean_dec_ref(x_369);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_370);
lean_inc(x_49);
x_371 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_49, x_370, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec_ref(x_371);
x_372 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_373, 0);
lean_inc(x_375);
lean_dec(x_373);
lean_inc(x_49);
x_376 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_376, 0, x_49);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_377 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_375, x_376, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
lean_dec_ref(x_377);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_st_ref_take(x_3);
x_382 = lean_ctor_get(x_381, 1);
lean_inc_ref(x_382);
x_383 = lean_ctor_get(x_381, 2);
lean_inc(x_383);
x_384 = lean_ctor_get(x_381, 3);
lean_inc(x_384);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 lean_ctor_release(x_381, 2);
 lean_ctor_release(x_381, 3);
 x_385 = x_381;
} else {
 lean_dec_ref(x_381);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(0, 4, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_380);
lean_ctor_set(x_386, 1, x_382);
lean_ctor_set(x_386, 2, x_383);
lean_ctor_set(x_386, 3, x_384);
x_387 = lean_st_ref_set(x_3, x_386);
x_388 = lean_unbox(x_379);
lean_dec(x_379);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_370);
lean_dec(x_49);
lean_dec(x_1);
x_389 = lean_st_ref_take(x_3);
x_390 = lean_ctor_get(x_389, 0);
lean_inc_ref(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc_ref(x_391);
x_392 = lean_ctor_get(x_389, 2);
lean_inc(x_392);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_393 = x_389;
} else {
 lean_dec_ref(x_389);
 x_393 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(0, 4, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_390);
lean_ctor_set(x_394, 1, x_391);
lean_ctor_set(x_394, 2, x_392);
lean_ctor_set(x_394, 3, x_37);
x_395 = lean_st_ref_set(x_3, x_394);
x_396 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 x_398 = x_396;
} else {
 lean_dec_ref(x_396);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_399 = lean_alloc_ctor(1, 1, 0);
} else {
 x_399 = x_374;
 lean_ctor_set_tag(x_399, 1);
}
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_2, 0, x_399);
if (lean_is_scalar(x_398)) {
 x_400 = lean_alloc_ctor(0, 1, 0);
} else {
 x_400 = x_398;
}
lean_ctor_set(x_400, 0, x_2);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_374);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_401 = lean_ctor_get(x_396, 0);
lean_inc(x_401);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 x_402 = x_396;
} else {
 lean_dec_ref(x_396);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 1, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_401);
return x_403;
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_34);
lean_inc(x_370);
x_404 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_404, 0, x_370);
x_405 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_405, 0, x_404);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_406 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_49, x_405, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
lean_dec_ref(x_406);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; 
lean_dec(x_1);
lean_inc(x_370);
x_408 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_370, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_409 = x_408;
} else {
 lean_dec_ref(x_408);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_410 = lean_alloc_ctor(1, 1, 0);
} else {
 x_410 = x_374;
 lean_ctor_set_tag(x_410, 1);
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_32, 0, x_370);
lean_ctor_set(x_2, 0, x_410);
if (lean_is_scalar(x_409)) {
 x_411 = lean_alloc_ctor(0, 1, 0);
} else {
 x_411 = x_409;
}
lean_ctor_set(x_411, 0, x_2);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_374);
lean_dec(x_370);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_412 = lean_ctor_get(x_408, 0);
lean_inc(x_412);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_413 = x_408;
} else {
 lean_dec_ref(x_408);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 1, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_412);
return x_414;
}
}
else
{
lean_object* x_415; lean_object* x_416; 
lean_dec(x_374);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_415 = lean_ctor_get(x_407, 0);
lean_inc(x_415);
lean_dec_ref(x_407);
lean_ctor_set(x_32, 1, x_415);
lean_ctor_set(x_32, 0, x_370);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_416 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_416;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_374);
lean_dec(x_370);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_417 = lean_ctor_get(x_406, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_418 = x_406;
} else {
 lean_dec_ref(x_406);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 1, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_417);
return x_419;
}
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_374);
lean_dec(x_370);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_420 = lean_ctor_get(x_377, 0);
lean_inc(x_420);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_421 = x_377;
} else {
 lean_dec_ref(x_377);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_420);
return x_422;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_370);
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_423 = lean_ctor_get(x_371, 0);
lean_inc(x_423);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_424 = x_371;
} else {
 lean_dec_ref(x_371);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 1, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_49);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_426 = lean_ctor_get(x_369, 0);
lean_inc(x_426);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 x_427 = x_369;
} else {
 lean_dec_ref(x_369);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 1, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_426);
return x_428;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_429 = lean_ctor_get(x_45, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_45, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_431 = x_45;
} else {
 lean_dec_ref(x_45);
 x_431 = lean_box(0);
}
x_432 = lean_st_ref_take(x_3);
x_433 = lean_ctor_get(x_432, 1);
lean_inc_ref(x_433);
x_434 = lean_ctor_get(x_432, 2);
lean_inc(x_434);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 x_435 = x_432;
} else {
 lean_dec_ref(x_432);
 x_435 = lean_box(0);
}
lean_inc(x_47);
lean_ctor_set(x_36, 3, x_430);
lean_inc(x_37);
if (lean_is_scalar(x_431)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_431;
}
lean_ctor_set(x_436, 0, x_36);
lean_ctor_set(x_436, 1, x_37);
if (lean_is_scalar(x_435)) {
 x_437 = lean_alloc_ctor(0, 4, 0);
} else {
 x_437 = x_435;
}
lean_ctor_set(x_437, 0, x_429);
lean_ctor_set(x_437, 1, x_433);
lean_ctor_set(x_437, 2, x_434);
lean_ctor_set(x_437, 3, x_436);
x_438 = lean_st_ref_set(x_3, x_437);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_47);
x_439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_439, 0, x_38);
lean_ctor_set(x_2, 0, x_439);
x_440 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_440, 0, x_2);
return x_440;
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_inc(x_49);
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_37);
lean_dec_ref(x_16);
x_441 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
lean_dec_ref(x_441);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
lean_dec(x_442);
lean_inc(x_34);
x_444 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_444, 0, x_49);
lean_closure_set(x_444, 1, x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_445 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_443, x_444, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
lean_dec_ref(x_445);
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
lean_dec(x_446);
x_448 = lean_st_ref_take(x_3);
x_449 = lean_ctor_get(x_448, 1);
lean_inc_ref(x_449);
x_450 = lean_ctor_get(x_448, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_448, 3);
lean_inc(x_451);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 lean_ctor_release(x_448, 2);
 lean_ctor_release(x_448, 3);
 x_452 = x_448;
} else {
 lean_dec_ref(x_448);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(0, 4, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_447);
lean_ctor_set(x_453, 1, x_449);
lean_ctor_set(x_453, 2, x_450);
lean_ctor_set(x_453, 3, x_451);
x_454 = lean_st_ref_set(x_3, x_453);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_455 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_455;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_456 = lean_ctor_get(x_445, 0);
lean_inc(x_456);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 x_457 = x_445;
} else {
 lean_dec_ref(x_445);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 1, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_456);
return x_458;
}
}
}
}
else
{
uint8_t x_459; 
lean_free_object(x_36);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_459 = !lean_is_exclusive(x_52);
if (x_459 == 0)
{
return x_52;
}
else
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_ctor_get(x_52, 0);
lean_inc(x_460);
lean_dec(x_52);
x_461 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_461, 0, x_460);
return x_461;
}
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_462 = lean_ctor_get(x_38, 0);
x_463 = lean_ctor_get(x_36, 0);
x_464 = lean_ctor_get(x_36, 2);
x_465 = lean_ctor_get(x_36, 3);
x_466 = lean_ctor_get(x_36, 4);
x_467 = lean_ctor_get(x_36, 5);
lean_inc(x_467);
lean_inc(x_466);
lean_inc(x_465);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_36);
x_468 = lean_ctor_get(x_39, 0);
x_469 = lean_ctor_get(x_462, 0);
lean_inc(x_469);
lean_dec(x_462);
lean_inc(x_468);
x_470 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_470, 0, x_468);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_471 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_469, x_470, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 x_473 = x_471;
} else {
 lean_dec_ref(x_471);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_472, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_472, 1);
lean_inc(x_475);
lean_dec(x_472);
x_476 = lean_st_ref_take(x_3);
x_477 = lean_ctor_get(x_476, 1);
lean_inc_ref(x_477);
x_478 = lean_ctor_get(x_476, 2);
lean_inc(x_478);
x_479 = lean_ctor_get(x_476, 3);
lean_inc(x_479);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 x_480 = x_476;
} else {
 lean_dec_ref(x_476);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(0, 4, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_475);
lean_ctor_set(x_481, 1, x_477);
lean_ctor_set(x_481, 2, x_478);
lean_ctor_set(x_481, 3, x_479);
x_482 = lean_st_ref_set(x_3, x_481);
x_483 = lean_ctor_get(x_474, 1);
lean_inc_ref(x_483);
lean_dec(x_474);
x_484 = lean_local_ctx_num_indices(x_483);
x_485 = lean_nat_dec_lt(x_35, x_484);
lean_dec(x_484);
if (x_485 == 0)
{
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_486; 
lean_dec(x_473);
lean_inc(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_463);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_486 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_464, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
lean_dec_ref(x_486);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_487);
lean_inc(x_468);
x_488 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_468, x_487, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec_ref(x_488);
x_489 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 x_491 = x_489;
} else {
 lean_dec_ref(x_489);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_490, 0);
lean_inc(x_492);
lean_dec(x_490);
lean_inc(x_468);
x_493 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_493, 0, x_468);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_494 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_492, x_493, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
lean_dec_ref(x_494);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_498 = lean_st_ref_take(x_3);
x_499 = lean_ctor_get(x_498, 1);
lean_inc_ref(x_499);
x_500 = lean_ctor_get(x_498, 2);
lean_inc(x_500);
x_501 = lean_ctor_get(x_498, 3);
lean_inc(x_501);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 lean_ctor_release(x_498, 2);
 lean_ctor_release(x_498, 3);
 x_502 = x_498;
} else {
 lean_dec_ref(x_498);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(0, 4, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_497);
lean_ctor_set(x_503, 1, x_499);
lean_ctor_set(x_503, 2, x_500);
lean_ctor_set(x_503, 3, x_501);
x_504 = lean_st_ref_set(x_3, x_503);
x_505 = lean_unbox(x_496);
lean_dec(x_496);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_487);
lean_dec(x_468);
lean_dec(x_1);
x_506 = lean_st_ref_take(x_3);
x_507 = lean_ctor_get(x_506, 0);
lean_inc_ref(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc_ref(x_508);
x_509 = lean_ctor_get(x_506, 2);
lean_inc(x_509);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 lean_ctor_release(x_506, 2);
 lean_ctor_release(x_506, 3);
 x_510 = x_506;
} else {
 lean_dec_ref(x_506);
 x_510 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(0, 4, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_507);
lean_ctor_set(x_511, 1, x_508);
lean_ctor_set(x_511, 2, x_509);
lean_ctor_set(x_511, 3, x_37);
x_512 = lean_st_ref_set(x_3, x_511);
x_513 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 x_515 = x_513;
} else {
 lean_dec_ref(x_513);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_516 = lean_alloc_ctor(1, 1, 0);
} else {
 x_516 = x_491;
 lean_ctor_set_tag(x_516, 1);
}
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_2, 0, x_516);
if (lean_is_scalar(x_515)) {
 x_517 = lean_alloc_ctor(0, 1, 0);
} else {
 x_517 = x_515;
}
lean_ctor_set(x_517, 0, x_2);
return x_517;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_491);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_518 = lean_ctor_get(x_513, 0);
lean_inc(x_518);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 x_519 = x_513;
} else {
 lean_dec_ref(x_513);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 1, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_518);
return x_520;
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_34);
lean_inc(x_487);
x_521 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_521, 0, x_487);
x_522 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_522, 0, x_521);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_523 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_468, x_522, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
lean_dec_ref(x_523);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; 
lean_dec(x_1);
lean_inc(x_487);
x_525 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_487, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 x_526 = x_525;
} else {
 lean_dec_ref(x_525);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_527 = lean_alloc_ctor(1, 1, 0);
} else {
 x_527 = x_491;
 lean_ctor_set_tag(x_527, 1);
}
lean_ctor_set(x_527, 0, x_524);
lean_ctor_set(x_32, 0, x_487);
lean_ctor_set(x_2, 0, x_527);
if (lean_is_scalar(x_526)) {
 x_528 = lean_alloc_ctor(0, 1, 0);
} else {
 x_528 = x_526;
}
lean_ctor_set(x_528, 0, x_2);
return x_528;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_491);
lean_dec(x_487);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_529 = lean_ctor_get(x_525, 0);
lean_inc(x_529);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 x_530 = x_525;
} else {
 lean_dec_ref(x_525);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(1, 1, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_529);
return x_531;
}
}
else
{
lean_object* x_532; lean_object* x_533; 
lean_dec(x_491);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_532 = lean_ctor_get(x_524, 0);
lean_inc(x_532);
lean_dec_ref(x_524);
lean_ctor_set(x_32, 1, x_532);
lean_ctor_set(x_32, 0, x_487);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_533 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_533;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_491);
lean_dec(x_487);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_534 = lean_ctor_get(x_523, 0);
lean_inc(x_534);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 x_535 = x_523;
} else {
 lean_dec_ref(x_523);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 1, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_534);
return x_536;
}
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_491);
lean_dec(x_487);
lean_dec(x_468);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_537 = lean_ctor_get(x_494, 0);
lean_inc(x_537);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 x_538 = x_494;
} else {
 lean_dec_ref(x_494);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 1, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_537);
return x_539;
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_487);
lean_dec(x_468);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_540 = lean_ctor_get(x_488, 0);
lean_inc(x_540);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 x_541 = x_488;
} else {
 lean_dec_ref(x_488);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 1, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_468);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_543 = lean_ctor_get(x_486, 0);
lean_inc(x_543);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_544 = x_486;
} else {
 lean_dec_ref(x_486);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 1, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_543);
return x_545;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_546 = lean_ctor_get(x_465, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_465, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_548 = x_465;
} else {
 lean_dec_ref(x_465);
 x_548 = lean_box(0);
}
x_549 = lean_st_ref_take(x_3);
x_550 = lean_ctor_get(x_549, 1);
lean_inc_ref(x_550);
x_551 = lean_ctor_get(x_549, 2);
lean_inc(x_551);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 lean_ctor_release(x_549, 2);
 lean_ctor_release(x_549, 3);
 x_552 = x_549;
} else {
 lean_dec_ref(x_549);
 x_552 = lean_box(0);
}
lean_inc(x_467);
x_553 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_553, 0, x_463);
lean_ctor_set(x_553, 1, x_39);
lean_ctor_set(x_553, 2, x_464);
lean_ctor_set(x_553, 3, x_547);
lean_ctor_set(x_553, 4, x_466);
lean_ctor_set(x_553, 5, x_467);
lean_inc(x_37);
if (lean_is_scalar(x_548)) {
 x_554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_554 = x_548;
}
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_37);
if (lean_is_scalar(x_552)) {
 x_555 = lean_alloc_ctor(0, 4, 0);
} else {
 x_555 = x_552;
}
lean_ctor_set(x_555, 0, x_546);
lean_ctor_set(x_555, 1, x_550);
lean_ctor_set(x_555, 2, x_551);
lean_ctor_set(x_555, 3, x_554);
x_556 = lean_st_ref_set(x_3, x_555);
lean_dec(x_3);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_467);
x_557 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_557, 0, x_38);
lean_ctor_set(x_2, 0, x_557);
if (lean_is_scalar(x_473)) {
 x_558 = lean_alloc_ctor(0, 1, 0);
} else {
 x_558 = x_473;
}
lean_ctor_set(x_558, 0, x_2);
return x_558;
}
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_473);
lean_inc(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec_ref(x_464);
lean_dec(x_463);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_inc(x_37);
lean_dec_ref(x_16);
x_559 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
lean_dec_ref(x_559);
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
lean_dec(x_560);
lean_inc(x_34);
x_562 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_562, 0, x_468);
lean_closure_set(x_562, 1, x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_563 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_561, x_562, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
lean_dec_ref(x_563);
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
lean_dec(x_564);
x_566 = lean_st_ref_take(x_3);
x_567 = lean_ctor_get(x_566, 1);
lean_inc_ref(x_567);
x_568 = lean_ctor_get(x_566, 2);
lean_inc(x_568);
x_569 = lean_ctor_get(x_566, 3);
lean_inc(x_569);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 lean_ctor_release(x_566, 2);
 lean_ctor_release(x_566, 3);
 x_570 = x_566;
} else {
 lean_dec_ref(x_566);
 x_570 = lean_box(0);
}
if (lean_is_scalar(x_570)) {
 x_571 = lean_alloc_ctor(0, 4, 0);
} else {
 x_571 = x_570;
}
lean_ctor_set(x_571, 0, x_565);
lean_ctor_set(x_571, 1, x_567);
lean_ctor_set(x_571, 2, x_568);
lean_ctor_set(x_571, 3, x_569);
x_572 = lean_st_ref_set(x_3, x_571);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_573 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_573;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_574 = lean_ctor_get(x_563, 0);
lean_inc(x_574);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 x_575 = x_563;
} else {
 lean_dec_ref(x_563);
 x_575 = lean_box(0);
}
if (lean_is_scalar(x_575)) {
 x_576 = lean_alloc_ctor(1, 1, 0);
} else {
 x_576 = x_575;
}
lean_ctor_set(x_576, 0, x_574);
return x_576;
}
}
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec_ref(x_464);
lean_dec(x_463);
lean_free_object(x_38);
lean_dec_ref(x_39);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_577 = lean_ctor_get(x_471, 0);
lean_inc(x_577);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 x_578 = x_471;
} else {
 lean_dec_ref(x_471);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(1, 1, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_577);
return x_579;
}
}
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_580 = lean_ctor_get(x_38, 0);
lean_inc(x_580);
lean_dec(x_38);
x_581 = lean_ctor_get(x_36, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_36, 2);
lean_inc_ref(x_582);
x_583 = lean_ctor_get(x_36, 3);
lean_inc(x_583);
x_584 = lean_ctor_get(x_36, 4);
lean_inc_ref(x_584);
x_585 = lean_ctor_get(x_36, 5);
lean_inc(x_585);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 x_586 = x_36;
} else {
 lean_dec_ref(x_36);
 x_586 = lean_box(0);
}
x_587 = lean_ctor_get(x_39, 0);
x_588 = lean_ctor_get(x_580, 0);
lean_inc(x_588);
lean_dec(x_580);
lean_inc(x_587);
x_589 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_589, 0, x_587);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_590 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_588, x_589, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 x_592 = x_590;
} else {
 lean_dec_ref(x_590);
 x_592 = lean_box(0);
}
x_593 = lean_ctor_get(x_591, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_591, 1);
lean_inc(x_594);
lean_dec(x_591);
x_595 = lean_st_ref_take(x_3);
x_596 = lean_ctor_get(x_595, 1);
lean_inc_ref(x_596);
x_597 = lean_ctor_get(x_595, 2);
lean_inc(x_597);
x_598 = lean_ctor_get(x_595, 3);
lean_inc(x_598);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 lean_ctor_release(x_595, 2);
 lean_ctor_release(x_595, 3);
 x_599 = x_595;
} else {
 lean_dec_ref(x_595);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(0, 4, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_594);
lean_ctor_set(x_600, 1, x_596);
lean_ctor_set(x_600, 2, x_597);
lean_ctor_set(x_600, 3, x_598);
x_601 = lean_st_ref_set(x_3, x_600);
x_602 = lean_ctor_get(x_593, 1);
lean_inc_ref(x_602);
lean_dec(x_593);
x_603 = lean_local_ctx_num_indices(x_602);
x_604 = lean_nat_dec_lt(x_35, x_603);
lean_dec(x_603);
if (x_604 == 0)
{
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_605; 
lean_dec(x_592);
lean_inc(x_587);
lean_dec(x_586);
lean_dec(x_585);
lean_dec_ref(x_584);
lean_dec(x_581);
lean_dec_ref(x_39);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_605 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_582, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
lean_dec_ref(x_605);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_606);
lean_inc(x_587);
x_607 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_587, x_606, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec_ref(x_607);
x_608 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 x_610 = x_608;
} else {
 lean_dec_ref(x_608);
 x_610 = lean_box(0);
}
x_611 = lean_ctor_get(x_609, 0);
lean_inc(x_611);
lean_dec(x_609);
lean_inc(x_587);
x_612 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_612, 0, x_587);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_613 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_611, x_612, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
lean_dec_ref(x_613);
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
x_617 = lean_st_ref_take(x_3);
x_618 = lean_ctor_get(x_617, 1);
lean_inc_ref(x_618);
x_619 = lean_ctor_get(x_617, 2);
lean_inc(x_619);
x_620 = lean_ctor_get(x_617, 3);
lean_inc(x_620);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 lean_ctor_release(x_617, 2);
 lean_ctor_release(x_617, 3);
 x_621 = x_617;
} else {
 lean_dec_ref(x_617);
 x_621 = lean_box(0);
}
if (lean_is_scalar(x_621)) {
 x_622 = lean_alloc_ctor(0, 4, 0);
} else {
 x_622 = x_621;
}
lean_ctor_set(x_622, 0, x_616);
lean_ctor_set(x_622, 1, x_618);
lean_ctor_set(x_622, 2, x_619);
lean_ctor_set(x_622, 3, x_620);
x_623 = lean_st_ref_set(x_3, x_622);
x_624 = lean_unbox(x_615);
lean_dec(x_615);
if (x_624 == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_606);
lean_dec(x_587);
lean_dec(x_1);
x_625 = lean_st_ref_take(x_3);
x_626 = lean_ctor_get(x_625, 0);
lean_inc_ref(x_626);
x_627 = lean_ctor_get(x_625, 1);
lean_inc_ref(x_627);
x_628 = lean_ctor_get(x_625, 2);
lean_inc(x_628);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 lean_ctor_release(x_625, 2);
 lean_ctor_release(x_625, 3);
 x_629 = x_625;
} else {
 lean_dec_ref(x_625);
 x_629 = lean_box(0);
}
lean_inc(x_37);
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(0, 4, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_626);
lean_ctor_set(x_630, 1, x_627);
lean_ctor_set(x_630, 2, x_628);
lean_ctor_set(x_630, 3, x_37);
x_631 = lean_st_ref_set(x_3, x_630);
x_632 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 x_634 = x_632;
} else {
 lean_dec_ref(x_632);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_635 = lean_alloc_ctor(1, 1, 0);
} else {
 x_635 = x_610;
 lean_ctor_set_tag(x_635, 1);
}
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_2, 0, x_635);
if (lean_is_scalar(x_634)) {
 x_636 = lean_alloc_ctor(0, 1, 0);
} else {
 x_636 = x_634;
}
lean_ctor_set(x_636, 0, x_2);
return x_636;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_610);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_637 = lean_ctor_get(x_632, 0);
lean_inc(x_637);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 x_638 = x_632;
} else {
 lean_dec_ref(x_632);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 1, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_34);
lean_inc(x_606);
x_640 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_640, 0, x_606);
x_641 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_641, 0, x_640);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_642 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_587, x_641, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_643; 
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
lean_dec_ref(x_642);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; 
lean_dec(x_1);
lean_inc(x_606);
x_644 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_606, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 x_645 = x_644;
} else {
 lean_dec_ref(x_644);
 x_645 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_646 = lean_alloc_ctor(1, 1, 0);
} else {
 x_646 = x_610;
 lean_ctor_set_tag(x_646, 1);
}
lean_ctor_set(x_646, 0, x_643);
lean_ctor_set(x_32, 0, x_606);
lean_ctor_set(x_2, 0, x_646);
if (lean_is_scalar(x_645)) {
 x_647 = lean_alloc_ctor(0, 1, 0);
} else {
 x_647 = x_645;
}
lean_ctor_set(x_647, 0, x_2);
return x_647;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec(x_610);
lean_dec(x_606);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_648 = lean_ctor_get(x_644, 0);
lean_inc(x_648);
if (lean_is_exclusive(x_644)) {
 lean_ctor_release(x_644, 0);
 x_649 = x_644;
} else {
 lean_dec_ref(x_644);
 x_649 = lean_box(0);
}
if (lean_is_scalar(x_649)) {
 x_650 = lean_alloc_ctor(1, 1, 0);
} else {
 x_650 = x_649;
}
lean_ctor_set(x_650, 0, x_648);
return x_650;
}
}
else
{
lean_object* x_651; lean_object* x_652; 
lean_dec(x_610);
lean_inc(x_37);
lean_dec(x_35);
lean_dec_ref(x_16);
x_651 = lean_ctor_get(x_643, 0);
lean_inc(x_651);
lean_dec_ref(x_643);
lean_ctor_set(x_32, 1, x_651);
lean_ctor_set(x_32, 0, x_606);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_652 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_652;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_610);
lean_dec(x_606);
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_653 = lean_ctor_get(x_642, 0);
lean_inc(x_653);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 x_654 = x_642;
} else {
 lean_dec_ref(x_642);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(1, 1, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_653);
return x_655;
}
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_610);
lean_dec(x_606);
lean_dec(x_587);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_656 = lean_ctor_get(x_613, 0);
lean_inc(x_656);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 x_657 = x_613;
} else {
 lean_dec_ref(x_613);
 x_657 = lean_box(0);
}
if (lean_is_scalar(x_657)) {
 x_658 = lean_alloc_ctor(1, 1, 0);
} else {
 x_658 = x_657;
}
lean_ctor_set(x_658, 0, x_656);
return x_658;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_606);
lean_dec(x_587);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_659 = lean_ctor_get(x_607, 0);
lean_inc(x_659);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 x_660 = x_607;
} else {
 lean_dec_ref(x_607);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 1, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_659);
return x_661;
}
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_587);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_662 = lean_ctor_get(x_605, 0);
lean_inc(x_662);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 x_663 = x_605;
} else {
 lean_dec_ref(x_605);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 1, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_662);
return x_664;
}
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_665 = lean_ctor_get(x_583, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_583, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_667 = x_583;
} else {
 lean_dec_ref(x_583);
 x_667 = lean_box(0);
}
x_668 = lean_st_ref_take(x_3);
x_669 = lean_ctor_get(x_668, 1);
lean_inc_ref(x_669);
x_670 = lean_ctor_get(x_668, 2);
lean_inc(x_670);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 lean_ctor_release(x_668, 2);
 lean_ctor_release(x_668, 3);
 x_671 = x_668;
} else {
 lean_dec_ref(x_668);
 x_671 = lean_box(0);
}
lean_inc(x_585);
if (lean_is_scalar(x_586)) {
 x_672 = lean_alloc_ctor(0, 6, 0);
} else {
 x_672 = x_586;
}
lean_ctor_set(x_672, 0, x_581);
lean_ctor_set(x_672, 1, x_39);
lean_ctor_set(x_672, 2, x_582);
lean_ctor_set(x_672, 3, x_666);
lean_ctor_set(x_672, 4, x_584);
lean_ctor_set(x_672, 5, x_585);
lean_inc(x_37);
if (lean_is_scalar(x_667)) {
 x_673 = lean_alloc_ctor(1, 2, 0);
} else {
 x_673 = x_667;
}
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_37);
if (lean_is_scalar(x_671)) {
 x_674 = lean_alloc_ctor(0, 4, 0);
} else {
 x_674 = x_671;
}
lean_ctor_set(x_674, 0, x_665);
lean_ctor_set(x_674, 1, x_669);
lean_ctor_set(x_674, 2, x_670);
lean_ctor_set(x_674, 3, x_673);
x_675 = lean_st_ref_set(x_3, x_674);
lean_dec(x_3);
x_676 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_676, 0, x_585);
x_677 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_2, 0, x_677);
if (lean_is_scalar(x_592)) {
 x_678 = lean_alloc_ctor(0, 1, 0);
} else {
 x_678 = x_592;
}
lean_ctor_set(x_678, 0, x_2);
return x_678;
}
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_592);
lean_inc(x_587);
lean_dec(x_586);
lean_dec(x_585);
lean_dec_ref(x_584);
lean_dec(x_583);
lean_dec_ref(x_582);
lean_dec(x_581);
lean_dec_ref(x_39);
lean_inc(x_37);
lean_dec_ref(x_16);
x_679 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
lean_dec_ref(x_679);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
lean_dec(x_680);
lean_inc(x_34);
x_682 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_682, 0, x_587);
lean_closure_set(x_682, 1, x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_683 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_681, x_682, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
lean_dec_ref(x_683);
x_685 = lean_ctor_get(x_684, 1);
lean_inc(x_685);
lean_dec(x_684);
x_686 = lean_st_ref_take(x_3);
x_687 = lean_ctor_get(x_686, 1);
lean_inc_ref(x_687);
x_688 = lean_ctor_get(x_686, 2);
lean_inc(x_688);
x_689 = lean_ctor_get(x_686, 3);
lean_inc(x_689);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 lean_ctor_release(x_686, 2);
 lean_ctor_release(x_686, 3);
 x_690 = x_686;
} else {
 lean_dec_ref(x_686);
 x_690 = lean_box(0);
}
if (lean_is_scalar(x_690)) {
 x_691 = lean_alloc_ctor(0, 4, 0);
} else {
 x_691 = x_690;
}
lean_ctor_set(x_691, 0, x_685);
lean_ctor_set(x_691, 1, x_687);
lean_ctor_set(x_691, 2, x_688);
lean_ctor_set(x_691, 3, x_689);
x_692 = lean_st_ref_set(x_3, x_691);
lean_ctor_set(x_13, 0, x_37);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_693 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_693;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_694 = lean_ctor_get(x_683, 0);
lean_inc(x_694);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 x_695 = x_683;
} else {
 lean_dec_ref(x_683);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 1, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_694);
return x_696;
}
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_586);
lean_dec(x_585);
lean_dec_ref(x_584);
lean_dec(x_583);
lean_dec_ref(x_582);
lean_dec(x_581);
lean_dec_ref(x_39);
lean_free_object(x_32);
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_697 = lean_ctor_get(x_590, 0);
lean_inc(x_697);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 x_698 = x_590;
} else {
 lean_dec_ref(x_590);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 1, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_697);
return x_699;
}
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_700 = lean_ctor_get(x_32, 0);
x_701 = lean_ctor_get(x_32, 1);
lean_inc(x_701);
lean_inc(x_700);
lean_dec(x_32);
x_702 = lean_ctor_get(x_16, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_16, 1);
x_704 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_705 = lean_ctor_get(x_702, 1);
lean_inc_ref(x_705);
x_706 = lean_ctor_get(x_704, 0);
lean_inc(x_706);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 x_707 = x_704;
} else {
 lean_dec_ref(x_704);
 x_707 = lean_box(0);
}
x_708 = lean_ctor_get(x_702, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_702, 2);
lean_inc_ref(x_709);
x_710 = lean_ctor_get(x_702, 3);
lean_inc(x_710);
x_711 = lean_ctor_get(x_702, 4);
lean_inc_ref(x_711);
x_712 = lean_ctor_get(x_702, 5);
lean_inc(x_712);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 lean_ctor_release(x_702, 2);
 lean_ctor_release(x_702, 3);
 lean_ctor_release(x_702, 4);
 lean_ctor_release(x_702, 5);
 x_713 = x_702;
} else {
 lean_dec_ref(x_702);
 x_713 = lean_box(0);
}
x_714 = lean_ctor_get(x_705, 0);
x_715 = lean_ctor_get(x_706, 0);
lean_inc(x_715);
lean_dec(x_706);
lean_inc(x_714);
x_716 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_716, 0, x_714);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_717 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_715, x_716, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; uint8_t x_731; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 x_719 = x_717;
} else {
 lean_dec_ref(x_717);
 x_719 = lean_box(0);
}
x_720 = lean_ctor_get(x_718, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_718, 1);
lean_inc(x_721);
lean_dec(x_718);
x_722 = lean_st_ref_take(x_3);
x_723 = lean_ctor_get(x_722, 1);
lean_inc_ref(x_723);
x_724 = lean_ctor_get(x_722, 2);
lean_inc(x_724);
x_725 = lean_ctor_get(x_722, 3);
lean_inc(x_725);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 lean_ctor_release(x_722, 1);
 lean_ctor_release(x_722, 2);
 lean_ctor_release(x_722, 3);
 x_726 = x_722;
} else {
 lean_dec_ref(x_722);
 x_726 = lean_box(0);
}
if (lean_is_scalar(x_726)) {
 x_727 = lean_alloc_ctor(0, 4, 0);
} else {
 x_727 = x_726;
}
lean_ctor_set(x_727, 0, x_721);
lean_ctor_set(x_727, 1, x_723);
lean_ctor_set(x_727, 2, x_724);
lean_ctor_set(x_727, 3, x_725);
x_728 = lean_st_ref_set(x_3, x_727);
x_729 = lean_ctor_get(x_720, 1);
lean_inc_ref(x_729);
lean_dec(x_720);
x_730 = lean_local_ctx_num_indices(x_729);
x_731 = lean_nat_dec_lt(x_701, x_730);
lean_dec(x_730);
if (x_731 == 0)
{
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_732; 
lean_dec(x_719);
lean_inc(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec(x_708);
lean_dec(x_707);
lean_dec_ref(x_705);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_732 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_709, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; lean_object* x_734; 
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
lean_dec_ref(x_732);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_733);
lean_inc(x_714);
x_734 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_714, x_733, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec_ref(x_734);
x_735 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 x_737 = x_735;
} else {
 lean_dec_ref(x_735);
 x_737 = lean_box(0);
}
x_738 = lean_ctor_get(x_736, 0);
lean_inc(x_738);
lean_dec(x_736);
lean_inc(x_714);
x_739 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_739, 0, x_714);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_740 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_738, x_739, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_740) == 0)
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; 
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
lean_dec_ref(x_740);
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
x_744 = lean_st_ref_take(x_3);
x_745 = lean_ctor_get(x_744, 1);
lean_inc_ref(x_745);
x_746 = lean_ctor_get(x_744, 2);
lean_inc(x_746);
x_747 = lean_ctor_get(x_744, 3);
lean_inc(x_747);
if (lean_is_exclusive(x_744)) {
 lean_ctor_release(x_744, 0);
 lean_ctor_release(x_744, 1);
 lean_ctor_release(x_744, 2);
 lean_ctor_release(x_744, 3);
 x_748 = x_744;
} else {
 lean_dec_ref(x_744);
 x_748 = lean_box(0);
}
if (lean_is_scalar(x_748)) {
 x_749 = lean_alloc_ctor(0, 4, 0);
} else {
 x_749 = x_748;
}
lean_ctor_set(x_749, 0, x_743);
lean_ctor_set(x_749, 1, x_745);
lean_ctor_set(x_749, 2, x_746);
lean_ctor_set(x_749, 3, x_747);
x_750 = lean_st_ref_set(x_3, x_749);
x_751 = lean_unbox(x_742);
lean_dec(x_742);
if (x_751 == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
lean_dec(x_733);
lean_dec(x_714);
lean_dec(x_1);
x_752 = lean_st_ref_take(x_3);
x_753 = lean_ctor_get(x_752, 0);
lean_inc_ref(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc_ref(x_754);
x_755 = lean_ctor_get(x_752, 2);
lean_inc(x_755);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 lean_ctor_release(x_752, 2);
 lean_ctor_release(x_752, 3);
 x_756 = x_752;
} else {
 lean_dec_ref(x_752);
 x_756 = lean_box(0);
}
lean_inc(x_703);
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(0, 4, 0);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_753);
lean_ctor_set(x_757, 1, x_754);
lean_ctor_set(x_757, 2, x_755);
lean_ctor_set(x_757, 3, x_703);
x_758 = lean_st_ref_set(x_3, x_757);
x_759 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 x_761 = x_759;
} else {
 lean_dec_ref(x_759);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_762 = lean_alloc_ctor(1, 1, 0);
} else {
 x_762 = x_737;
 lean_ctor_set_tag(x_762, 1);
}
lean_ctor_set(x_762, 0, x_760);
x_763 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_763, 0, x_700);
lean_ctor_set(x_763, 1, x_701);
lean_ctor_set(x_13, 1, x_763);
lean_ctor_set(x_2, 0, x_762);
if (lean_is_scalar(x_761)) {
 x_764 = lean_alloc_ctor(0, 1, 0);
} else {
 x_764 = x_761;
}
lean_ctor_set(x_764, 0, x_2);
return x_764;
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; 
lean_dec(x_737);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_765 = lean_ctor_get(x_759, 0);
lean_inc(x_765);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 x_766 = x_759;
} else {
 lean_dec_ref(x_759);
 x_766 = lean_box(0);
}
if (lean_is_scalar(x_766)) {
 x_767 = lean_alloc_ctor(1, 1, 0);
} else {
 x_767 = x_766;
}
lean_ctor_set(x_767, 0, x_765);
return x_767;
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_700);
lean_inc(x_733);
x_768 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_768, 0, x_733);
x_769 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_769, 0, x_768);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_770 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_714, x_769, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_770) == 0)
{
lean_object* x_771; 
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
lean_dec_ref(x_770);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; 
lean_dec(x_1);
lean_inc(x_733);
x_772 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_733, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_772) == 0)
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 x_773 = x_772;
} else {
 lean_dec_ref(x_772);
 x_773 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_774 = lean_alloc_ctor(1, 1, 0);
} else {
 x_774 = x_737;
 lean_ctor_set_tag(x_774, 1);
}
lean_ctor_set(x_774, 0, x_771);
x_775 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_775, 0, x_733);
lean_ctor_set(x_775, 1, x_701);
lean_ctor_set(x_13, 1, x_775);
lean_ctor_set(x_2, 0, x_774);
if (lean_is_scalar(x_773)) {
 x_776 = lean_alloc_ctor(0, 1, 0);
} else {
 x_776 = x_773;
}
lean_ctor_set(x_776, 0, x_2);
return x_776;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
lean_dec(x_737);
lean_dec(x_733);
lean_dec(x_701);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
x_777 = lean_ctor_get(x_772, 0);
lean_inc(x_777);
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 x_778 = x_772;
} else {
 lean_dec_ref(x_772);
 x_778 = lean_box(0);
}
if (lean_is_scalar(x_778)) {
 x_779 = lean_alloc_ctor(1, 1, 0);
} else {
 x_779 = x_778;
}
lean_ctor_set(x_779, 0, x_777);
return x_779;
}
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
lean_dec(x_737);
lean_inc(x_703);
lean_dec(x_701);
lean_dec_ref(x_16);
x_780 = lean_ctor_get(x_771, 0);
lean_inc(x_780);
lean_dec_ref(x_771);
x_781 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_781, 0, x_733);
lean_ctor_set(x_781, 1, x_780);
lean_ctor_set(x_13, 1, x_781);
lean_ctor_set(x_13, 0, x_703);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_782 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_782;
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
lean_dec(x_737);
lean_dec(x_733);
lean_dec(x_701);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_783 = lean_ctor_get(x_770, 0);
lean_inc(x_783);
if (lean_is_exclusive(x_770)) {
 lean_ctor_release(x_770, 0);
 x_784 = x_770;
} else {
 lean_dec_ref(x_770);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(1, 1, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_783);
return x_785;
}
}
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
lean_dec(x_737);
lean_dec(x_733);
lean_dec(x_714);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_786 = lean_ctor_get(x_740, 0);
lean_inc(x_786);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 x_787 = x_740;
} else {
 lean_dec_ref(x_740);
 x_787 = lean_box(0);
}
if (lean_is_scalar(x_787)) {
 x_788 = lean_alloc_ctor(1, 1, 0);
} else {
 x_788 = x_787;
}
lean_ctor_set(x_788, 0, x_786);
return x_788;
}
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
lean_dec(x_733);
lean_dec(x_714);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_789 = lean_ctor_get(x_734, 0);
lean_inc(x_789);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 x_790 = x_734;
} else {
 lean_dec_ref(x_734);
 x_790 = lean_box(0);
}
if (lean_is_scalar(x_790)) {
 x_791 = lean_alloc_ctor(1, 1, 0);
} else {
 x_791 = x_790;
}
lean_ctor_set(x_791, 0, x_789);
return x_791;
}
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_714);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_792 = lean_ctor_get(x_732, 0);
lean_inc(x_792);
if (lean_is_exclusive(x_732)) {
 lean_ctor_release(x_732, 0);
 x_793 = x_732;
} else {
 lean_dec_ref(x_732);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 1, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_792);
return x_794;
}
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_795 = lean_ctor_get(x_710, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_710, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_797 = x_710;
} else {
 lean_dec_ref(x_710);
 x_797 = lean_box(0);
}
x_798 = lean_st_ref_take(x_3);
x_799 = lean_ctor_get(x_798, 1);
lean_inc_ref(x_799);
x_800 = lean_ctor_get(x_798, 2);
lean_inc(x_800);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 lean_ctor_release(x_798, 2);
 lean_ctor_release(x_798, 3);
 x_801 = x_798;
} else {
 lean_dec_ref(x_798);
 x_801 = lean_box(0);
}
lean_inc(x_712);
if (lean_is_scalar(x_713)) {
 x_802 = lean_alloc_ctor(0, 6, 0);
} else {
 x_802 = x_713;
}
lean_ctor_set(x_802, 0, x_708);
lean_ctor_set(x_802, 1, x_705);
lean_ctor_set(x_802, 2, x_709);
lean_ctor_set(x_802, 3, x_796);
lean_ctor_set(x_802, 4, x_711);
lean_ctor_set(x_802, 5, x_712);
lean_inc(x_703);
if (lean_is_scalar(x_797)) {
 x_803 = lean_alloc_ctor(1, 2, 0);
} else {
 x_803 = x_797;
}
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_703);
if (lean_is_scalar(x_801)) {
 x_804 = lean_alloc_ctor(0, 4, 0);
} else {
 x_804 = x_801;
}
lean_ctor_set(x_804, 0, x_795);
lean_ctor_set(x_804, 1, x_799);
lean_ctor_set(x_804, 2, x_800);
lean_ctor_set(x_804, 3, x_803);
x_805 = lean_st_ref_set(x_3, x_804);
lean_dec(x_3);
if (lean_is_scalar(x_707)) {
 x_806 = lean_alloc_ctor(1, 1, 0);
} else {
 x_806 = x_707;
 lean_ctor_set_tag(x_806, 1);
}
lean_ctor_set(x_806, 0, x_712);
x_807 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_807, 0, x_806);
x_808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_808, 0, x_700);
lean_ctor_set(x_808, 1, x_701);
lean_ctor_set(x_13, 1, x_808);
lean_ctor_set(x_2, 0, x_807);
if (lean_is_scalar(x_719)) {
 x_809 = lean_alloc_ctor(0, 1, 0);
} else {
 x_809 = x_719;
}
lean_ctor_set(x_809, 0, x_2);
return x_809;
}
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_dec(x_719);
lean_inc(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec(x_707);
lean_dec_ref(x_705);
lean_inc(x_703);
lean_dec_ref(x_16);
x_810 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
lean_dec_ref(x_810);
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
lean_dec(x_811);
lean_inc(x_700);
x_813 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_813, 0, x_714);
lean_closure_set(x_813, 1, x_700);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_814 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_812, x_813, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_815 = lean_ctor_get(x_814, 0);
lean_inc(x_815);
lean_dec_ref(x_814);
x_816 = lean_ctor_get(x_815, 1);
lean_inc(x_816);
lean_dec(x_815);
x_817 = lean_st_ref_take(x_3);
x_818 = lean_ctor_get(x_817, 1);
lean_inc_ref(x_818);
x_819 = lean_ctor_get(x_817, 2);
lean_inc(x_819);
x_820 = lean_ctor_get(x_817, 3);
lean_inc(x_820);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 lean_ctor_release(x_817, 2);
 lean_ctor_release(x_817, 3);
 x_821 = x_817;
} else {
 lean_dec_ref(x_817);
 x_821 = lean_box(0);
}
if (lean_is_scalar(x_821)) {
 x_822 = lean_alloc_ctor(0, 4, 0);
} else {
 x_822 = x_821;
}
lean_ctor_set(x_822, 0, x_816);
lean_ctor_set(x_822, 1, x_818);
lean_ctor_set(x_822, 2, x_819);
lean_ctor_set(x_822, 3, x_820);
x_823 = lean_st_ref_set(x_3, x_822);
x_824 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_824, 0, x_700);
lean_ctor_set(x_824, 1, x_701);
lean_ctor_set(x_13, 1, x_824);
lean_ctor_set(x_13, 0, x_703);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
x_825 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_825;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
lean_dec(x_703);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_826 = lean_ctor_get(x_814, 0);
lean_inc(x_826);
if (lean_is_exclusive(x_814)) {
 lean_ctor_release(x_814, 0);
 x_827 = x_814;
} else {
 lean_dec_ref(x_814);
 x_827 = lean_box(0);
}
if (lean_is_scalar(x_827)) {
 x_828 = lean_alloc_ctor(1, 1, 0);
} else {
 x_828 = x_827;
}
lean_ctor_set(x_828, 0, x_826);
return x_828;
}
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; 
lean_dec(x_713);
lean_dec(x_712);
lean_dec_ref(x_711);
lean_dec(x_710);
lean_dec_ref(x_709);
lean_dec(x_708);
lean_dec(x_707);
lean_dec_ref(x_705);
lean_dec(x_701);
lean_dec(x_700);
lean_free_object(x_13);
lean_dec_ref(x_16);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_829 = lean_ctor_get(x_717, 0);
lean_inc(x_829);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 x_830 = x_717;
} else {
 lean_dec_ref(x_717);
 x_830 = lean_box(0);
}
if (lean_is_scalar(x_830)) {
 x_831 = lean_alloc_ctor(1, 1, 0);
} else {
 x_831 = x_830;
}
lean_ctor_set(x_831, 0, x_829);
return x_831;
}
}
}
}
else
{
lean_object* x_832; lean_object* x_833; 
x_832 = lean_ctor_get(x_13, 1);
x_833 = lean_ctor_get(x_13, 0);
lean_inc(x_832);
lean_inc(x_833);
lean_dec(x_13);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_834 = lean_ctor_get(x_832, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_832, 1);
lean_inc(x_835);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_836 = x_832;
} else {
 lean_dec_ref(x_832);
 x_836 = lean_box(0);
}
x_837 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_3);
lean_dec(x_3);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 x_838 = x_837;
} else {
 lean_dec_ref(x_837);
 x_838 = lean_box(0);
}
x_839 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
if (lean_is_scalar(x_836)) {
 x_840 = lean_alloc_ctor(0, 2, 0);
} else {
 x_840 = x_836;
}
lean_ctor_set(x_840, 0, x_834);
lean_ctor_set(x_840, 1, x_835);
x_841 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_841, 0, x_833);
lean_ctor_set(x_841, 1, x_840);
lean_ctor_set(x_2, 1, x_841);
lean_ctor_set(x_2, 0, x_839);
if (lean_is_scalar(x_838)) {
 x_842 = lean_alloc_ctor(0, 1, 0);
} else {
 x_842 = x_838;
}
lean_ctor_set(x_842, 0, x_2);
return x_842;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_843 = lean_ctor_get(x_832, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_832, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_845 = x_832;
} else {
 lean_dec_ref(x_832);
 x_845 = lean_box(0);
}
x_846 = lean_ctor_get(x_833, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_833, 1);
x_848 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_849 = lean_ctor_get(x_846, 1);
lean_inc_ref(x_849);
x_850 = lean_ctor_get(x_848, 0);
lean_inc(x_850);
if (lean_is_exclusive(x_848)) {
 lean_ctor_release(x_848, 0);
 x_851 = x_848;
} else {
 lean_dec_ref(x_848);
 x_851 = lean_box(0);
}
x_852 = lean_ctor_get(x_846, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_846, 2);
lean_inc_ref(x_853);
x_854 = lean_ctor_get(x_846, 3);
lean_inc(x_854);
x_855 = lean_ctor_get(x_846, 4);
lean_inc_ref(x_855);
x_856 = lean_ctor_get(x_846, 5);
lean_inc(x_856);
if (lean_is_exclusive(x_846)) {
 lean_ctor_release(x_846, 0);
 lean_ctor_release(x_846, 1);
 lean_ctor_release(x_846, 2);
 lean_ctor_release(x_846, 3);
 lean_ctor_release(x_846, 4);
 lean_ctor_release(x_846, 5);
 x_857 = x_846;
} else {
 lean_dec_ref(x_846);
 x_857 = lean_box(0);
}
x_858 = lean_ctor_get(x_849, 0);
x_859 = lean_ctor_get(x_850, 0);
lean_inc(x_859);
lean_dec(x_850);
lean_inc(x_858);
x_860 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_860, 0, x_858);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_861 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_859, x_860, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; uint8_t x_875; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
if (lean_is_exclusive(x_861)) {
 lean_ctor_release(x_861, 0);
 x_863 = x_861;
} else {
 lean_dec_ref(x_861);
 x_863 = lean_box(0);
}
x_864 = lean_ctor_get(x_862, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_862, 1);
lean_inc(x_865);
lean_dec(x_862);
x_866 = lean_st_ref_take(x_3);
x_867 = lean_ctor_get(x_866, 1);
lean_inc_ref(x_867);
x_868 = lean_ctor_get(x_866, 2);
lean_inc(x_868);
x_869 = lean_ctor_get(x_866, 3);
lean_inc(x_869);
if (lean_is_exclusive(x_866)) {
 lean_ctor_release(x_866, 0);
 lean_ctor_release(x_866, 1);
 lean_ctor_release(x_866, 2);
 lean_ctor_release(x_866, 3);
 x_870 = x_866;
} else {
 lean_dec_ref(x_866);
 x_870 = lean_box(0);
}
if (lean_is_scalar(x_870)) {
 x_871 = lean_alloc_ctor(0, 4, 0);
} else {
 x_871 = x_870;
}
lean_ctor_set(x_871, 0, x_865);
lean_ctor_set(x_871, 1, x_867);
lean_ctor_set(x_871, 2, x_868);
lean_ctor_set(x_871, 3, x_869);
x_872 = lean_st_ref_set(x_3, x_871);
x_873 = lean_ctor_get(x_864, 1);
lean_inc_ref(x_873);
lean_dec(x_864);
x_874 = lean_local_ctx_num_indices(x_873);
x_875 = lean_nat_dec_lt(x_844, x_874);
lean_dec(x_874);
if (x_875 == 0)
{
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_876; 
lean_dec(x_863);
lean_inc(x_858);
lean_dec(x_857);
lean_dec(x_856);
lean_dec_ref(x_855);
lean_dec(x_852);
lean_dec(x_851);
lean_dec_ref(x_849);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_876 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_853, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
lean_dec_ref(x_876);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_877);
lean_inc(x_858);
x_878 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_858, x_877, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec_ref(x_878);
x_879 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_880 = lean_ctor_get(x_879, 0);
lean_inc(x_880);
if (lean_is_exclusive(x_879)) {
 lean_ctor_release(x_879, 0);
 x_881 = x_879;
} else {
 lean_dec_ref(x_879);
 x_881 = lean_box(0);
}
x_882 = lean_ctor_get(x_880, 0);
lean_inc(x_882);
lean_dec(x_880);
lean_inc(x_858);
x_883 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_883, 0, x_858);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_884 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_882, x_883, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; uint8_t x_895; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
lean_dec_ref(x_884);
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
lean_dec(x_885);
x_888 = lean_st_ref_take(x_3);
x_889 = lean_ctor_get(x_888, 1);
lean_inc_ref(x_889);
x_890 = lean_ctor_get(x_888, 2);
lean_inc(x_890);
x_891 = lean_ctor_get(x_888, 3);
lean_inc(x_891);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 lean_ctor_release(x_888, 2);
 lean_ctor_release(x_888, 3);
 x_892 = x_888;
} else {
 lean_dec_ref(x_888);
 x_892 = lean_box(0);
}
if (lean_is_scalar(x_892)) {
 x_893 = lean_alloc_ctor(0, 4, 0);
} else {
 x_893 = x_892;
}
lean_ctor_set(x_893, 0, x_887);
lean_ctor_set(x_893, 1, x_889);
lean_ctor_set(x_893, 2, x_890);
lean_ctor_set(x_893, 3, x_891);
x_894 = lean_st_ref_set(x_3, x_893);
x_895 = lean_unbox(x_886);
lean_dec(x_886);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; 
lean_dec(x_877);
lean_dec(x_858);
lean_dec(x_1);
x_896 = lean_st_ref_take(x_3);
x_897 = lean_ctor_get(x_896, 0);
lean_inc_ref(x_897);
x_898 = lean_ctor_get(x_896, 1);
lean_inc_ref(x_898);
x_899 = lean_ctor_get(x_896, 2);
lean_inc(x_899);
if (lean_is_exclusive(x_896)) {
 lean_ctor_release(x_896, 0);
 lean_ctor_release(x_896, 1);
 lean_ctor_release(x_896, 2);
 lean_ctor_release(x_896, 3);
 x_900 = x_896;
} else {
 lean_dec_ref(x_896);
 x_900 = lean_box(0);
}
lean_inc(x_847);
if (lean_is_scalar(x_900)) {
 x_901 = lean_alloc_ctor(0, 4, 0);
} else {
 x_901 = x_900;
}
lean_ctor_set(x_901, 0, x_897);
lean_ctor_set(x_901, 1, x_898);
lean_ctor_set(x_901, 2, x_899);
lean_ctor_set(x_901, 3, x_847);
x_902 = lean_st_ref_set(x_3, x_901);
x_903 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 x_905 = x_903;
} else {
 lean_dec_ref(x_903);
 x_905 = lean_box(0);
}
if (lean_is_scalar(x_881)) {
 x_906 = lean_alloc_ctor(1, 1, 0);
} else {
 x_906 = x_881;
 lean_ctor_set_tag(x_906, 1);
}
lean_ctor_set(x_906, 0, x_904);
if (lean_is_scalar(x_845)) {
 x_907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_907 = x_845;
}
lean_ctor_set(x_907, 0, x_843);
lean_ctor_set(x_907, 1, x_844);
x_908 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_908, 0, x_833);
lean_ctor_set(x_908, 1, x_907);
lean_ctor_set(x_2, 1, x_908);
lean_ctor_set(x_2, 0, x_906);
if (lean_is_scalar(x_905)) {
 x_909 = lean_alloc_ctor(0, 1, 0);
} else {
 x_909 = x_905;
}
lean_ctor_set(x_909, 0, x_2);
return x_909;
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; 
lean_dec(x_881);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec_ref(x_833);
lean_free_object(x_2);
x_910 = lean_ctor_get(x_903, 0);
lean_inc(x_910);
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 x_911 = x_903;
} else {
 lean_dec_ref(x_903);
 x_911 = lean_box(0);
}
if (lean_is_scalar(x_911)) {
 x_912 = lean_alloc_ctor(1, 1, 0);
} else {
 x_912 = x_911;
}
lean_ctor_set(x_912, 0, x_910);
return x_912;
}
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; 
lean_dec(x_843);
lean_inc(x_877);
x_913 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_913, 0, x_877);
x_914 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_914, 0, x_913);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_915 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_858, x_914, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
lean_dec_ref(x_915);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; 
lean_dec(x_1);
lean_inc(x_877);
x_917 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_877, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_917) == 0)
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 x_918 = x_917;
} else {
 lean_dec_ref(x_917);
 x_918 = lean_box(0);
}
if (lean_is_scalar(x_881)) {
 x_919 = lean_alloc_ctor(1, 1, 0);
} else {
 x_919 = x_881;
 lean_ctor_set_tag(x_919, 1);
}
lean_ctor_set(x_919, 0, x_916);
if (lean_is_scalar(x_845)) {
 x_920 = lean_alloc_ctor(0, 2, 0);
} else {
 x_920 = x_845;
}
lean_ctor_set(x_920, 0, x_877);
lean_ctor_set(x_920, 1, x_844);
x_921 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_921, 0, x_833);
lean_ctor_set(x_921, 1, x_920);
lean_ctor_set(x_2, 1, x_921);
lean_ctor_set(x_2, 0, x_919);
if (lean_is_scalar(x_918)) {
 x_922 = lean_alloc_ctor(0, 1, 0);
} else {
 x_922 = x_918;
}
lean_ctor_set(x_922, 0, x_2);
return x_922;
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_881);
lean_dec(x_877);
lean_dec(x_845);
lean_dec(x_844);
lean_dec_ref(x_833);
lean_free_object(x_2);
x_923 = lean_ctor_get(x_917, 0);
lean_inc(x_923);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 x_924 = x_917;
} else {
 lean_dec_ref(x_917);
 x_924 = lean_box(0);
}
if (lean_is_scalar(x_924)) {
 x_925 = lean_alloc_ctor(1, 1, 0);
} else {
 x_925 = x_924;
}
lean_ctor_set(x_925, 0, x_923);
return x_925;
}
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
lean_dec(x_881);
lean_inc(x_847);
lean_dec(x_844);
lean_dec_ref(x_833);
x_926 = lean_ctor_get(x_916, 0);
lean_inc(x_926);
lean_dec_ref(x_916);
if (lean_is_scalar(x_845)) {
 x_927 = lean_alloc_ctor(0, 2, 0);
} else {
 x_927 = x_845;
}
lean_ctor_set(x_927, 0, x_877);
lean_ctor_set(x_927, 1, x_926);
x_928 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_928, 0, x_847);
lean_ctor_set(x_928, 1, x_927);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_928);
lean_ctor_set(x_2, 0, x_1);
x_929 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_929;
}
}
else
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; 
lean_dec(x_881);
lean_dec(x_877);
lean_dec(x_845);
lean_dec(x_844);
lean_dec_ref(x_833);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_930 = lean_ctor_get(x_915, 0);
lean_inc(x_930);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 x_931 = x_915;
} else {
 lean_dec_ref(x_915);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(1, 1, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_930);
return x_932;
}
}
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; 
lean_dec(x_881);
lean_dec(x_877);
lean_dec(x_858);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec_ref(x_833);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_933 = lean_ctor_get(x_884, 0);
lean_inc(x_933);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 x_934 = x_884;
} else {
 lean_dec_ref(x_884);
 x_934 = lean_box(0);
}
if (lean_is_scalar(x_934)) {
 x_935 = lean_alloc_ctor(1, 1, 0);
} else {
 x_935 = x_934;
}
lean_ctor_set(x_935, 0, x_933);
return x_935;
}
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_877);
lean_dec(x_858);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec_ref(x_833);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_936 = lean_ctor_get(x_878, 0);
lean_inc(x_936);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 x_937 = x_878;
} else {
 lean_dec_ref(x_878);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(1, 1, 0);
} else {
 x_938 = x_937;
}
lean_ctor_set(x_938, 0, x_936);
return x_938;
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_858);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec_ref(x_833);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_939 = lean_ctor_get(x_876, 0);
lean_inc(x_939);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 x_940 = x_876;
} else {
 lean_dec_ref(x_876);
 x_940 = lean_box(0);
}
if (lean_is_scalar(x_940)) {
 x_941 = lean_alloc_ctor(1, 1, 0);
} else {
 x_941 = x_940;
}
lean_ctor_set(x_941, 0, x_939);
return x_941;
}
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_942 = lean_ctor_get(x_854, 0);
lean_inc(x_942);
x_943 = lean_ctor_get(x_854, 1);
lean_inc(x_943);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_944 = x_854;
} else {
 lean_dec_ref(x_854);
 x_944 = lean_box(0);
}
x_945 = lean_st_ref_take(x_3);
x_946 = lean_ctor_get(x_945, 1);
lean_inc_ref(x_946);
x_947 = lean_ctor_get(x_945, 2);
lean_inc(x_947);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 lean_ctor_release(x_945, 2);
 lean_ctor_release(x_945, 3);
 x_948 = x_945;
} else {
 lean_dec_ref(x_945);
 x_948 = lean_box(0);
}
lean_inc(x_856);
if (lean_is_scalar(x_857)) {
 x_949 = lean_alloc_ctor(0, 6, 0);
} else {
 x_949 = x_857;
}
lean_ctor_set(x_949, 0, x_852);
lean_ctor_set(x_949, 1, x_849);
lean_ctor_set(x_949, 2, x_853);
lean_ctor_set(x_949, 3, x_943);
lean_ctor_set(x_949, 4, x_855);
lean_ctor_set(x_949, 5, x_856);
lean_inc(x_847);
if (lean_is_scalar(x_944)) {
 x_950 = lean_alloc_ctor(1, 2, 0);
} else {
 x_950 = x_944;
}
lean_ctor_set(x_950, 0, x_949);
lean_ctor_set(x_950, 1, x_847);
if (lean_is_scalar(x_948)) {
 x_951 = lean_alloc_ctor(0, 4, 0);
} else {
 x_951 = x_948;
}
lean_ctor_set(x_951, 0, x_942);
lean_ctor_set(x_951, 1, x_946);
lean_ctor_set(x_951, 2, x_947);
lean_ctor_set(x_951, 3, x_950);
x_952 = lean_st_ref_set(x_3, x_951);
lean_dec(x_3);
if (lean_is_scalar(x_851)) {
 x_953 = lean_alloc_ctor(1, 1, 0);
} else {
 x_953 = x_851;
 lean_ctor_set_tag(x_953, 1);
}
lean_ctor_set(x_953, 0, x_856);
x_954 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_954, 0, x_953);
if (lean_is_scalar(x_845)) {
 x_955 = lean_alloc_ctor(0, 2, 0);
} else {
 x_955 = x_845;
}
lean_ctor_set(x_955, 0, x_843);
lean_ctor_set(x_955, 1, x_844);
x_956 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_956, 0, x_833);
lean_ctor_set(x_956, 1, x_955);
lean_ctor_set(x_2, 1, x_956);
lean_ctor_set(x_2, 0, x_954);
if (lean_is_scalar(x_863)) {
 x_957 = lean_alloc_ctor(0, 1, 0);
} else {
 x_957 = x_863;
}
lean_ctor_set(x_957, 0, x_2);
return x_957;
}
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
lean_dec(x_863);
lean_inc(x_858);
lean_dec(x_857);
lean_dec(x_856);
lean_dec_ref(x_855);
lean_dec(x_854);
lean_dec_ref(x_853);
lean_dec(x_852);
lean_dec(x_851);
lean_dec_ref(x_849);
lean_inc(x_847);
lean_dec_ref(x_833);
x_958 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
lean_dec_ref(x_958);
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
lean_dec(x_959);
lean_inc(x_843);
x_961 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_961, 0, x_858);
lean_closure_set(x_961, 1, x_843);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_962 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_960, x_961, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_962) == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_963 = lean_ctor_get(x_962, 0);
lean_inc(x_963);
lean_dec_ref(x_962);
x_964 = lean_ctor_get(x_963, 1);
lean_inc(x_964);
lean_dec(x_963);
x_965 = lean_st_ref_take(x_3);
x_966 = lean_ctor_get(x_965, 1);
lean_inc_ref(x_966);
x_967 = lean_ctor_get(x_965, 2);
lean_inc(x_967);
x_968 = lean_ctor_get(x_965, 3);
lean_inc(x_968);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 lean_ctor_release(x_965, 2);
 lean_ctor_release(x_965, 3);
 x_969 = x_965;
} else {
 lean_dec_ref(x_965);
 x_969 = lean_box(0);
}
if (lean_is_scalar(x_969)) {
 x_970 = lean_alloc_ctor(0, 4, 0);
} else {
 x_970 = x_969;
}
lean_ctor_set(x_970, 0, x_964);
lean_ctor_set(x_970, 1, x_966);
lean_ctor_set(x_970, 2, x_967);
lean_ctor_set(x_970, 3, x_968);
x_971 = lean_st_ref_set(x_3, x_970);
if (lean_is_scalar(x_845)) {
 x_972 = lean_alloc_ctor(0, 2, 0);
} else {
 x_972 = x_845;
}
lean_ctor_set(x_972, 0, x_843);
lean_ctor_set(x_972, 1, x_844);
x_973 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_973, 0, x_847);
lean_ctor_set(x_973, 1, x_972);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_973);
lean_ctor_set(x_2, 0, x_1);
x_974 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_974;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; 
lean_dec(x_847);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_975 = lean_ctor_get(x_962, 0);
lean_inc(x_975);
if (lean_is_exclusive(x_962)) {
 lean_ctor_release(x_962, 0);
 x_976 = x_962;
} else {
 lean_dec_ref(x_962);
 x_976 = lean_box(0);
}
if (lean_is_scalar(x_976)) {
 x_977 = lean_alloc_ctor(1, 1, 0);
} else {
 x_977 = x_976;
}
lean_ctor_set(x_977, 0, x_975);
return x_977;
}
}
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; 
lean_dec(x_857);
lean_dec(x_856);
lean_dec_ref(x_855);
lean_dec(x_854);
lean_dec_ref(x_853);
lean_dec(x_852);
lean_dec(x_851);
lean_dec_ref(x_849);
lean_dec(x_845);
lean_dec(x_844);
lean_dec(x_843);
lean_dec_ref(x_833);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_978 = lean_ctor_get(x_861, 0);
lean_inc(x_978);
if (lean_is_exclusive(x_861)) {
 lean_ctor_release(x_861, 0);
 x_979 = x_861;
} else {
 lean_dec_ref(x_861);
 x_979 = lean_box(0);
}
if (lean_is_scalar(x_979)) {
 x_980 = lean_alloc_ctor(1, 1, 0);
} else {
 x_980 = x_979;
}
lean_ctor_set(x_980, 0, x_978);
return x_980;
}
}
}
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_981 = lean_ctor_get(x_2, 1);
lean_inc(x_981);
lean_dec(x_2);
x_982 = lean_ctor_get(x_981, 1);
lean_inc(x_982);
x_983 = lean_ctor_get(x_981, 0);
lean_inc(x_983);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 lean_ctor_release(x_981, 1);
 x_984 = x_981;
} else {
 lean_dec_ref(x_981);
 x_984 = lean_box(0);
}
if (lean_obj_tag(x_983) == 0)
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_985 = lean_ctor_get(x_982, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_982, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_982)) {
 lean_ctor_release(x_982, 0);
 lean_ctor_release(x_982, 1);
 x_987 = x_982;
} else {
 lean_dec_ref(x_982);
 x_987 = lean_box(0);
}
x_988 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_resetChoiceStack___redArg(x_3);
lean_dec(x_3);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 x_989 = x_988;
} else {
 lean_dec_ref(x_988);
 x_989 = lean_box(0);
}
x_990 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0;
if (lean_is_scalar(x_987)) {
 x_991 = lean_alloc_ctor(0, 2, 0);
} else {
 x_991 = x_987;
}
lean_ctor_set(x_991, 0, x_985);
lean_ctor_set(x_991, 1, x_986);
if (lean_is_scalar(x_984)) {
 x_992 = lean_alloc_ctor(0, 2, 0);
} else {
 x_992 = x_984;
}
lean_ctor_set(x_992, 0, x_983);
lean_ctor_set(x_992, 1, x_991);
x_993 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_993, 0, x_990);
lean_ctor_set(x_993, 1, x_992);
if (lean_is_scalar(x_989)) {
 x_994 = lean_alloc_ctor(0, 1, 0);
} else {
 x_994 = x_989;
}
lean_ctor_set(x_994, 0, x_993);
return x_994;
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_995 = lean_ctor_get(x_982, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_982, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_982)) {
 lean_ctor_release(x_982, 0);
 lean_ctor_release(x_982, 1);
 x_997 = x_982;
} else {
 lean_dec_ref(x_982);
 x_997 = lean_box(0);
}
x_998 = lean_ctor_get(x_983, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_983, 1);
x_1000 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_1001 = lean_ctor_get(x_998, 1);
lean_inc_ref(x_1001);
x_1002 = lean_ctor_get(x_1000, 0);
lean_inc(x_1002);
if (lean_is_exclusive(x_1000)) {
 lean_ctor_release(x_1000, 0);
 x_1003 = x_1000;
} else {
 lean_dec_ref(x_1000);
 x_1003 = lean_box(0);
}
x_1004 = lean_ctor_get(x_998, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_998, 2);
lean_inc_ref(x_1005);
x_1006 = lean_ctor_get(x_998, 3);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_998, 4);
lean_inc_ref(x_1007);
x_1008 = lean_ctor_get(x_998, 5);
lean_inc(x_1008);
if (lean_is_exclusive(x_998)) {
 lean_ctor_release(x_998, 0);
 lean_ctor_release(x_998, 1);
 lean_ctor_release(x_998, 2);
 lean_ctor_release(x_998, 3);
 lean_ctor_release(x_998, 4);
 lean_ctor_release(x_998, 5);
 x_1009 = x_998;
} else {
 lean_dec_ref(x_998);
 x_1009 = lean_box(0);
}
x_1010 = lean_ctor_get(x_1001, 0);
x_1011 = lean_ctor_get(x_1002, 0);
lean_inc(x_1011);
lean_dec(x_1002);
lean_inc(x_1010);
x_1012 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed), 10, 1);
lean_closure_set(x_1012, 0, x_1010);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1013 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1011, x_1012, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1013) == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; uint8_t x_1027; 
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 x_1015 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1015 = lean_box(0);
}
x_1016 = lean_ctor_get(x_1014, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1014, 1);
lean_inc(x_1017);
lean_dec(x_1014);
x_1018 = lean_st_ref_take(x_3);
x_1019 = lean_ctor_get(x_1018, 1);
lean_inc_ref(x_1019);
x_1020 = lean_ctor_get(x_1018, 2);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1018, 3);
lean_inc(x_1021);
if (lean_is_exclusive(x_1018)) {
 lean_ctor_release(x_1018, 0);
 lean_ctor_release(x_1018, 1);
 lean_ctor_release(x_1018, 2);
 lean_ctor_release(x_1018, 3);
 x_1022 = x_1018;
} else {
 lean_dec_ref(x_1018);
 x_1022 = lean_box(0);
}
if (lean_is_scalar(x_1022)) {
 x_1023 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1023 = x_1022;
}
lean_ctor_set(x_1023, 0, x_1017);
lean_ctor_set(x_1023, 1, x_1019);
lean_ctor_set(x_1023, 2, x_1020);
lean_ctor_set(x_1023, 3, x_1021);
x_1024 = lean_st_ref_set(x_3, x_1023);
x_1025 = lean_ctor_get(x_1016, 1);
lean_inc_ref(x_1025);
lean_dec(x_1016);
x_1026 = lean_local_ctx_num_indices(x_1025);
x_1027 = lean_nat_dec_lt(x_996, x_1026);
lean_dec(x_1026);
if (x_1027 == 0)
{
if (lean_obj_tag(x_1006) == 0)
{
lean_object* x_1028; 
lean_dec(x_1015);
lean_inc(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec_ref(x_1007);
lean_dec(x_1004);
lean_dec(x_1003);
lean_dec_ref(x_1001);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1028 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_1005, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1028) == 0)
{
lean_object* x_1029; lean_object* x_1030; 
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
lean_dec_ref(x_1028);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1029);
lean_inc(x_1010);
x_1030 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1(x_1010, x_1029, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1030) == 0)
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
lean_dec_ref(x_1030);
x_1031 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 x_1033 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1033 = lean_box(0);
}
x_1034 = lean_ctor_get(x_1032, 0);
lean_inc(x_1034);
lean_dec(x_1032);
lean_inc(x_1010);
x_1035 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed), 10, 1);
lean_closure_set(x_1035, 0, x_1010);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1036 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1034, x_1035, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; uint8_t x_1047; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
lean_dec_ref(x_1036);
x_1038 = lean_ctor_get(x_1037, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1037, 1);
lean_inc(x_1039);
lean_dec(x_1037);
x_1040 = lean_st_ref_take(x_3);
x_1041 = lean_ctor_get(x_1040, 1);
lean_inc_ref(x_1041);
x_1042 = lean_ctor_get(x_1040, 2);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1040, 3);
lean_inc(x_1043);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 lean_ctor_release(x_1040, 2);
 lean_ctor_release(x_1040, 3);
 x_1044 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1044 = lean_box(0);
}
if (lean_is_scalar(x_1044)) {
 x_1045 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1045 = x_1044;
}
lean_ctor_set(x_1045, 0, x_1039);
lean_ctor_set(x_1045, 1, x_1041);
lean_ctor_set(x_1045, 2, x_1042);
lean_ctor_set(x_1045, 3, x_1043);
x_1046 = lean_st_ref_set(x_3, x_1045);
x_1047 = lean_unbox(x_1038);
lean_dec(x_1038);
if (x_1047 == 0)
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_1029);
lean_dec(x_1010);
lean_dec(x_1);
x_1048 = lean_st_ref_take(x_3);
x_1049 = lean_ctor_get(x_1048, 0);
lean_inc_ref(x_1049);
x_1050 = lean_ctor_get(x_1048, 1);
lean_inc_ref(x_1050);
x_1051 = lean_ctor_get(x_1048, 2);
lean_inc(x_1051);
if (lean_is_exclusive(x_1048)) {
 lean_ctor_release(x_1048, 0);
 lean_ctor_release(x_1048, 1);
 lean_ctor_release(x_1048, 2);
 lean_ctor_release(x_1048, 3);
 x_1052 = x_1048;
} else {
 lean_dec_ref(x_1048);
 x_1052 = lean_box(0);
}
lean_inc(x_999);
if (lean_is_scalar(x_1052)) {
 x_1053 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1053 = x_1052;
}
lean_ctor_set(x_1053, 0, x_1049);
lean_ctor_set(x_1053, 1, x_1050);
lean_ctor_set(x_1053, 2, x_1051);
lean_ctor_set(x_1053, 3, x_999);
x_1054 = lean_st_ref_set(x_3, x_1053);
x_1055 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1055) == 0)
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
x_1056 = lean_ctor_get(x_1055, 0);
lean_inc(x_1056);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 x_1057 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1057 = lean_box(0);
}
if (lean_is_scalar(x_1033)) {
 x_1058 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1058 = x_1033;
 lean_ctor_set_tag(x_1058, 1);
}
lean_ctor_set(x_1058, 0, x_1056);
if (lean_is_scalar(x_997)) {
 x_1059 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1059 = x_997;
}
lean_ctor_set(x_1059, 0, x_995);
lean_ctor_set(x_1059, 1, x_996);
if (lean_is_scalar(x_984)) {
 x_1060 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1060 = x_984;
}
lean_ctor_set(x_1060, 0, x_983);
lean_ctor_set(x_1060, 1, x_1059);
x_1061 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1061, 0, x_1058);
lean_ctor_set(x_1061, 1, x_1060);
if (lean_is_scalar(x_1057)) {
 x_1062 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1062 = x_1057;
}
lean_ctor_set(x_1062, 0, x_1061);
return x_1062;
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_1033);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec_ref(x_983);
x_1063 = lean_ctor_get(x_1055, 0);
lean_inc(x_1063);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 x_1064 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1064 = lean_box(0);
}
if (lean_is_scalar(x_1064)) {
 x_1065 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1065 = x_1064;
}
lean_ctor_set(x_1065, 0, x_1063);
return x_1065;
}
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_995);
lean_inc(x_1029);
x_1066 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed), 10, 1);
lean_closure_set(x_1066, 0, x_1029);
x_1067 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed), 10, 1);
lean_closure_set(x_1067, 0, x_1066);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1068 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1010, x_1067, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; 
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
lean_dec_ref(x_1068);
if (lean_obj_tag(x_1069) == 0)
{
lean_object* x_1070; 
lean_dec(x_1);
lean_inc(x_1029);
x_1070 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_1029, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 x_1071 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1071 = lean_box(0);
}
if (lean_is_scalar(x_1033)) {
 x_1072 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1072 = x_1033;
 lean_ctor_set_tag(x_1072, 1);
}
lean_ctor_set(x_1072, 0, x_1069);
if (lean_is_scalar(x_997)) {
 x_1073 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1073 = x_997;
}
lean_ctor_set(x_1073, 0, x_1029);
lean_ctor_set(x_1073, 1, x_996);
if (lean_is_scalar(x_984)) {
 x_1074 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1074 = x_984;
}
lean_ctor_set(x_1074, 0, x_983);
lean_ctor_set(x_1074, 1, x_1073);
x_1075 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1075, 0, x_1072);
lean_ctor_set(x_1075, 1, x_1074);
if (lean_is_scalar(x_1071)) {
 x_1076 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1076 = x_1071;
}
lean_ctor_set(x_1076, 0, x_1075);
return x_1076;
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
lean_dec(x_1033);
lean_dec(x_1029);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_984);
lean_dec_ref(x_983);
x_1077 = lean_ctor_get(x_1070, 0);
lean_inc(x_1077);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 x_1078 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1078 = lean_box(0);
}
if (lean_is_scalar(x_1078)) {
 x_1079 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1079 = x_1078;
}
lean_ctor_set(x_1079, 0, x_1077);
return x_1079;
}
}
else
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
lean_dec(x_1033);
lean_inc(x_999);
lean_dec(x_996);
lean_dec_ref(x_983);
x_1080 = lean_ctor_get(x_1069, 0);
lean_inc(x_1080);
lean_dec_ref(x_1069);
if (lean_is_scalar(x_997)) {
 x_1081 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1081 = x_997;
}
lean_ctor_set(x_1081, 0, x_1029);
lean_ctor_set(x_1081, 1, x_1080);
if (lean_is_scalar(x_984)) {
 x_1082 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1082 = x_984;
}
lean_ctor_set(x_1082, 0, x_999);
lean_ctor_set(x_1082, 1, x_1081);
lean_inc(x_1);
x_1083 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1083, 0, x_1);
lean_ctor_set(x_1083, 1, x_1082);
x_1084 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_1083, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_1084;
}
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_1033);
lean_dec(x_1029);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_984);
lean_dec_ref(x_983);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1085 = lean_ctor_get(x_1068, 0);
lean_inc(x_1085);
if (lean_is_exclusive(x_1068)) {
 lean_ctor_release(x_1068, 0);
 x_1086 = x_1068;
} else {
 lean_dec_ref(x_1068);
 x_1086 = lean_box(0);
}
if (lean_is_scalar(x_1086)) {
 x_1087 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1087 = x_1086;
}
lean_ctor_set(x_1087, 0, x_1085);
return x_1087;
}
}
}
else
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
lean_dec(x_1033);
lean_dec(x_1029);
lean_dec(x_1010);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec_ref(x_983);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1088 = lean_ctor_get(x_1036, 0);
lean_inc(x_1088);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 x_1089 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1089 = lean_box(0);
}
if (lean_is_scalar(x_1089)) {
 x_1090 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1090 = x_1089;
}
lean_ctor_set(x_1090, 0, x_1088);
return x_1090;
}
}
else
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
lean_dec(x_1029);
lean_dec(x_1010);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec_ref(x_983);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1091 = lean_ctor_get(x_1030, 0);
lean_inc(x_1091);
if (lean_is_exclusive(x_1030)) {
 lean_ctor_release(x_1030, 0);
 x_1092 = x_1030;
} else {
 lean_dec_ref(x_1030);
 x_1092 = lean_box(0);
}
if (lean_is_scalar(x_1092)) {
 x_1093 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1093 = x_1092;
}
lean_ctor_set(x_1093, 0, x_1091);
return x_1093;
}
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
lean_dec(x_1010);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec_ref(x_983);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1094 = lean_ctor_get(x_1028, 0);
lean_inc(x_1094);
if (lean_is_exclusive(x_1028)) {
 lean_ctor_release(x_1028, 0);
 x_1095 = x_1028;
} else {
 lean_dec_ref(x_1028);
 x_1095 = lean_box(0);
}
if (lean_is_scalar(x_1095)) {
 x_1096 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1096 = x_1095;
}
lean_ctor_set(x_1096, 0, x_1094);
return x_1096;
}
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1097 = lean_ctor_get(x_1006, 0);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1006, 1);
lean_inc(x_1098);
if (lean_is_exclusive(x_1006)) {
 lean_ctor_release(x_1006, 0);
 lean_ctor_release(x_1006, 1);
 x_1099 = x_1006;
} else {
 lean_dec_ref(x_1006);
 x_1099 = lean_box(0);
}
x_1100 = lean_st_ref_take(x_3);
x_1101 = lean_ctor_get(x_1100, 1);
lean_inc_ref(x_1101);
x_1102 = lean_ctor_get(x_1100, 2);
lean_inc(x_1102);
if (lean_is_exclusive(x_1100)) {
 lean_ctor_release(x_1100, 0);
 lean_ctor_release(x_1100, 1);
 lean_ctor_release(x_1100, 2);
 lean_ctor_release(x_1100, 3);
 x_1103 = x_1100;
} else {
 lean_dec_ref(x_1100);
 x_1103 = lean_box(0);
}
lean_inc(x_1008);
if (lean_is_scalar(x_1009)) {
 x_1104 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1104 = x_1009;
}
lean_ctor_set(x_1104, 0, x_1004);
lean_ctor_set(x_1104, 1, x_1001);
lean_ctor_set(x_1104, 2, x_1005);
lean_ctor_set(x_1104, 3, x_1098);
lean_ctor_set(x_1104, 4, x_1007);
lean_ctor_set(x_1104, 5, x_1008);
lean_inc(x_999);
if (lean_is_scalar(x_1099)) {
 x_1105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1105 = x_1099;
}
lean_ctor_set(x_1105, 0, x_1104);
lean_ctor_set(x_1105, 1, x_999);
if (lean_is_scalar(x_1103)) {
 x_1106 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1106 = x_1103;
}
lean_ctor_set(x_1106, 0, x_1097);
lean_ctor_set(x_1106, 1, x_1101);
lean_ctor_set(x_1106, 2, x_1102);
lean_ctor_set(x_1106, 3, x_1105);
x_1107 = lean_st_ref_set(x_3, x_1106);
lean_dec(x_3);
if (lean_is_scalar(x_1003)) {
 x_1108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1108 = x_1003;
 lean_ctor_set_tag(x_1108, 1);
}
lean_ctor_set(x_1108, 0, x_1008);
x_1109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1109, 0, x_1108);
if (lean_is_scalar(x_997)) {
 x_1110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1110 = x_997;
}
lean_ctor_set(x_1110, 0, x_995);
lean_ctor_set(x_1110, 1, x_996);
if (lean_is_scalar(x_984)) {
 x_1111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1111 = x_984;
}
lean_ctor_set(x_1111, 0, x_983);
lean_ctor_set(x_1111, 1, x_1110);
x_1112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1112, 0, x_1109);
lean_ctor_set(x_1112, 1, x_1111);
if (lean_is_scalar(x_1015)) {
 x_1113 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1113 = x_1015;
}
lean_ctor_set(x_1113, 0, x_1112);
return x_1113;
}
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
lean_dec(x_1015);
lean_inc(x_1010);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec_ref(x_1007);
lean_dec(x_1006);
lean_dec_ref(x_1005);
lean_dec(x_1004);
lean_dec(x_1003);
lean_dec_ref(x_1001);
lean_inc(x_999);
lean_dec_ref(x_983);
x_1114 = l_Lean_Meta_Grind_getGoal___redArg(x_3);
x_1115 = lean_ctor_get(x_1114, 0);
lean_inc(x_1115);
lean_dec_ref(x_1114);
x_1116 = lean_ctor_get(x_1115, 0);
lean_inc(x_1116);
lean_dec(x_1115);
lean_inc(x_995);
x_1117 = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed), 11, 2);
lean_closure_set(x_1117, 0, x_1010);
lean_closure_set(x_1117, 1, x_995);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1118 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_1116, x_1117, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_1118) == 0)
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1119 = lean_ctor_get(x_1118, 0);
lean_inc(x_1119);
lean_dec_ref(x_1118);
x_1120 = lean_ctor_get(x_1119, 1);
lean_inc(x_1120);
lean_dec(x_1119);
x_1121 = lean_st_ref_take(x_3);
x_1122 = lean_ctor_get(x_1121, 1);
lean_inc_ref(x_1122);
x_1123 = lean_ctor_get(x_1121, 2);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1121, 3);
lean_inc(x_1124);
if (lean_is_exclusive(x_1121)) {
 lean_ctor_release(x_1121, 0);
 lean_ctor_release(x_1121, 1);
 lean_ctor_release(x_1121, 2);
 lean_ctor_release(x_1121, 3);
 x_1125 = x_1121;
} else {
 lean_dec_ref(x_1121);
 x_1125 = lean_box(0);
}
if (lean_is_scalar(x_1125)) {
 x_1126 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1126 = x_1125;
}
lean_ctor_set(x_1126, 0, x_1120);
lean_ctor_set(x_1126, 1, x_1122);
lean_ctor_set(x_1126, 2, x_1123);
lean_ctor_set(x_1126, 3, x_1124);
x_1127 = lean_st_ref_set(x_3, x_1126);
if (lean_is_scalar(x_997)) {
 x_1128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1128 = x_997;
}
lean_ctor_set(x_1128, 0, x_995);
lean_ctor_set(x_1128, 1, x_996);
if (lean_is_scalar(x_984)) {
 x_1129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1129 = x_984;
}
lean_ctor_set(x_1129, 0, x_999);
lean_ctor_set(x_1129, 1, x_1128);
lean_inc(x_1);
x_1130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1130, 0, x_1);
lean_ctor_set(x_1130, 1, x_1129);
x_1131 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_1130, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_1131;
}
else
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; 
lean_dec(x_999);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1132 = lean_ctor_get(x_1118, 0);
lean_inc(x_1132);
if (lean_is_exclusive(x_1118)) {
 lean_ctor_release(x_1118, 0);
 x_1133 = x_1118;
} else {
 lean_dec_ref(x_1118);
 x_1133 = lean_box(0);
}
if (lean_is_scalar(x_1133)) {
 x_1134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1134 = x_1133;
}
lean_ctor_set(x_1134, 0, x_1132);
return x_1134;
}
}
}
else
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec_ref(x_1007);
lean_dec(x_1006);
lean_dec_ref(x_1005);
lean_dec(x_1004);
lean_dec(x_1003);
lean_dec_ref(x_1001);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_995);
lean_dec(x_984);
lean_dec_ref(x_983);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_1135 = lean_ctor_get(x_1013, 0);
lean_inc(x_1135);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 x_1136 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1136 = lean_box(0);
}
if (lean_is_scalar(x_1136)) {
 x_1137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1137 = x_1136;
}
lean_ctor_set(x_1137, 0, x_1135);
return x_1137;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___redArg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_st_ref_get(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_st_mk_ref(x_12);
x_14 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_st_ref_get(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_st_mk_ref(x_12);
x_14 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_getGoal___redArg(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_2);
x_14 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
x_22 = lean_st_ref_set(x_2, x_19);
lean_dec(x_2);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 2);
x_25 = lean_ctor_get(x_19, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_st_ref_set(x_2, x_26);
lean_dec(x_2);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_take(x_2);
x_32 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_31, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 3);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 lean_ctor_release(x_31, 3);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 4, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
x_37 = lean_st_ref_set(x_2, x_36);
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_29);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Grind.nextGoal\?", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: goal.inconsistent\n  ", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Grind_nextGoal_x3f___closed__1;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(187u);
x_4 = l_Lean_Meta_Grind_nextGoal_x3f___closed__0;
x_5 = l_Lean_Meta_Grind_mkChoice___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_nextGoal_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(232u);
x_4 = l_Lean_Meta_Grind_nextGoal_x3f___closed__0;
x_5 = l_Lean_Meta_Grind_mkChoice___closed__1;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_st_ref_get(x_1);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_List_isEmpty___redArg(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_st_ref_get(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*17);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_14);
lean_dec(x_11);
x_16 = l_Lean_Meta_Grind_nextGoal_x3f___closed__2;
x_17 = l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1(x_16, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = l_Lean_Meta_Grind_getGoal___redArg(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_18);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_nextGoal_x3f___lam__0___boxed), 10, 1);
lean_closure_set(x_22, 0, x_18);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_21, x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_st_ref_take(x_1);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_27);
x_31 = lean_st_ref_set(x_1, x_28);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_32; 
lean_free_object(x_24);
lean_dec(x_18);
lean_dec(x_11);
x_32 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec_ref(x_26);
lean_inc(x_33);
x_34 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_nextGoal_x3f___lam__1___boxed), 10, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_nextGoal_x3f___lam__2___boxed), 10, 1);
lean_closure_set(x_35, 0, x_34);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_18, x_35, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_free_object(x_24);
lean_dec(x_11);
x_38 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_41; 
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_37);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec_ref(x_37);
x_46 = lean_box(0);
lean_ctor_set(x_24, 1, x_45);
lean_ctor_set(x_24, 0, x_33);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_24);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_49 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___redArg(x_46, x_48, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_free_object(x_49);
x_53 = l_Lean_Meta_Grind_nextGoal_x3f___closed__3;
x_54 = l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1(x_53, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_54;
}
else
{
lean_object* x_55; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec_ref(x_52);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_Meta_Grind_nextGoal_x3f___closed__3;
x_59 = l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1(x_58, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec_ref(x_57);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_49);
if (x_62 == 0)
{
return x_49;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_49, 0);
lean_inc(x_63);
lean_dec(x_49);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
lean_dec(x_33);
lean_free_object(x_24);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_28, 1);
x_66 = lean_ctor_get(x_28, 2);
x_67 = lean_ctor_get(x_28, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_28);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_27);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set(x_68, 2, x_66);
lean_ctor_set(x_68, 3, x_67);
x_69 = lean_st_ref_set(x_1, x_68);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_70; 
lean_free_object(x_24);
lean_dec(x_18);
lean_dec(x_11);
x_70 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_26, 0);
lean_inc(x_71);
lean_dec_ref(x_26);
lean_inc(x_71);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_nextGoal_x3f___lam__1___boxed), 10, 1);
lean_closure_set(x_72, 0, x_71);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_nextGoal_x3f___lam__2___boxed), 10, 1);
lean_closure_set(x_73, 0, x_72);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_74 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_18, x_73, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_free_object(x_24);
lean_dec(x_11);
x_76 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_71, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_77 = x_76;
} else {
 lean_dec_ref(x_76);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_80 = x_76;
} else {
 lean_dec_ref(x_76);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_75, 0);
lean_inc(x_82);
lean_dec_ref(x_75);
x_83 = lean_box(0);
lean_ctor_set(x_24, 1, x_82);
lean_ctor_set(x_24, 0, x_71);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_11);
lean_ctor_set(x_84, 1, x_24);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_86 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___redArg(x_83, x_85, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_88);
x_90 = l_Lean_Meta_Grind_nextGoal_x3f___closed__3;
x_91 = l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1(x_90, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_dec_ref(x_89);
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_95 = x_86;
} else {
 lean_dec_ref(x_86);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
}
}
else
{
lean_dec(x_71);
lean_free_object(x_24);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_74;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_24, 0);
x_98 = lean_ctor_get(x_24, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_24);
x_99 = lean_st_ref_take(x_1);
x_100 = lean_ctor_get(x_99, 1);
lean_inc_ref(x_100);
x_101 = lean_ctor_get(x_99, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 3);
lean_inc(x_102);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 x_103 = x_99;
} else {
 lean_dec_ref(x_99);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 4, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_100);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_102);
x_105 = lean_st_ref_set(x_1, x_104);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_106; 
lean_dec(x_18);
lean_dec(x_11);
x_106 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_97, 0);
lean_inc(x_107);
lean_dec_ref(x_97);
lean_inc(x_107);
x_108 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_nextGoal_x3f___lam__1___boxed), 10, 1);
lean_closure_set(x_108, 0, x_107);
x_109 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_nextGoal_x3f___lam__2___boxed), 10, 1);
lean_closure_set(x_109, 0, x_108);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_110 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_mkChoice_spec__0___redArg(x_18, x_109, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
lean_dec(x_11);
x_112 = l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_closeLastPending(x_107, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_113 = x_112;
} else {
 lean_dec_ref(x_112);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 1, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_111, 0);
lean_inc(x_118);
lean_dec_ref(x_111);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_107);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_11);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_123 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___redArg(x_119, x_122, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
x_127 = l_Lean_Meta_Grind_nextGoal_x3f___closed__3;
x_128 = l_panic___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__1(x_127, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
lean_dec_ref(x_126);
if (lean_is_scalar(x_125)) {
 x_130 = lean_alloc_ctor(0, 1, 0);
} else {
 x_130 = x_125;
}
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_ctor_get(x_123, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_132 = x_123;
} else {
 lean_dec_ref(x_123);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
return x_133;
}
}
}
else
{
lean_dec(x_107);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_110;
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_23);
if (x_134 == 0)
{
return x_23;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_23, 0);
lean_inc(x_135);
lean_dec(x_23);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_box(0);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___Lean_Meta_Grind_nextGoal_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_Meta_Grind_nextGoal_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_nextGoal_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_nextGoal_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_nextGoal_x3f___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_nextGoal_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_nextGoal_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_SearchM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedProofStep_default___closed__0 = _init_l_Lean_Meta_Grind_instInhabitedProofStep_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedProofStep_default___closed__0);
l_Lean_Meta_Grind_instInhabitedProofStep_default = _init_l_Lean_Meta_Grind_instInhabitedProofStep_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedProofStep_default);
l_Lean_Meta_Grind_instInhabitedProofStep = _init_l_Lean_Meta_Grind_instInhabitedProofStep();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedProofStep);
l_Lean_Meta_Grind_instInhabitedProofTrace_default = _init_l_Lean_Meta_Grind_instInhabitedProofTrace_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedProofTrace_default);
l_Lean_Meta_Grind_instInhabitedProofTrace = _init_l_Lean_Meta_Grind_instInhabitedProofTrace();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedProofTrace);
l_Lean_Meta_Grind_instInhabitedChoice_default___closed__0 = _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice_default___closed__0);
l_Lean_Meta_Grind_instInhabitedChoice_default___closed__1 = _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice_default___closed__1);
l_Lean_Meta_Grind_instInhabitedChoice_default___closed__2 = _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice_default___closed__2);
l_Lean_Meta_Grind_instInhabitedChoice_default___closed__3 = _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice_default___closed__3);
l_Lean_Meta_Grind_instInhabitedChoice_default___closed__4 = _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice_default___closed__4);
l_Lean_Meta_Grind_instInhabitedChoice_default___closed__5 = _init_l_Lean_Meta_Grind_instInhabitedChoice_default___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice_default___closed__5);
l_Lean_Meta_Grind_instInhabitedChoice_default = _init_l_Lean_Meta_Grind_instInhabitedChoice_default();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice_default);
l_Lean_Meta_Grind_instInhabitedChoice = _init_l_Lean_Meta_Grind_instInhabitedChoice();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedChoice);
l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__0 = _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__0);
l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1 = _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__1);
l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2 = _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__2);
l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3 = _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__3);
l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4 = _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__4);
l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5 = _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__5);
l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6 = _init_l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_withCurrGoalContext___redArg___closed__6);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__0 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__0);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__1 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__1);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__2 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__2);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__3 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__3);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__4 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__4);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__5 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__5);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__6 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__6);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__7 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__7);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__8 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__8);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__9 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__9);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__10 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__10);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__11 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__11);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__12 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__12);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__13 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__13);
l_Lean_Meta_Grind_liftGoalM___redArg___closed__14 = _init_l_Lean_Meta_Grind_liftGoalM___redArg___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_liftGoalM___redArg___closed__14);
l_Lean_Meta_Grind_instMonadLiftGoalMSearchM___closed__0 = _init_l_Lean_Meta_Grind_instMonadLiftGoalMSearchM___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_instMonadLiftGoalMSearchM___closed__0);
l_Lean_Meta_Grind_instMonadLiftGoalMSearchM = _init_l_Lean_Meta_Grind_instMonadLiftGoalMSearchM();
lean_mark_persistent(l_Lean_Meta_Grind_instMonadLiftGoalMSearchM);
l_Lean_Meta_Grind_SearchM_run___redArg___closed__0 = _init_l_Lean_Meta_Grind_SearchM_run___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_SearchM_run___redArg___closed__0);
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__0();
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__2 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_MVarId_assign___at___Lean_Meta_Grind_mkChoice_spec__1_spec__1_spec__1___redArg___closed__2);
l_Lean_Meta_Grind_mkChoice___closed__0 = _init_l_Lean_Meta_Grind_mkChoice___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__0);
l_Lean_Meta_Grind_mkChoice___closed__1 = _init_l_Lean_Meta_Grind_mkChoice___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__1);
l_Lean_Meta_Grind_mkChoice___closed__2 = _init_l_Lean_Meta_Grind_mkChoice___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__2);
l_Lean_Meta_Grind_mkChoice___closed__3 = _init_l_Lean_Meta_Grind_mkChoice___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__3);
l_Lean_Meta_Grind_mkChoice___closed__4 = _init_l_Lean_Meta_Grind_mkChoice___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_mkChoice___closed__4);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__2);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__3);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_findMaxFVarIdx_x3f___closed__4);
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f_spec__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_nextChronoGoal_x3f___closed__2);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__1);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__2);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__3);
l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_SearchM_0__Lean_Meta_Grind_getFalseProof_x3f___lam__0___closed__4);
l_Lean_Meta_Grind_nextGoal_x3f___closed__0 = _init_l_Lean_Meta_Grind_nextGoal_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___closed__0);
l_Lean_Meta_Grind_nextGoal_x3f___closed__1 = _init_l_Lean_Meta_Grind_nextGoal_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___closed__1);
l_Lean_Meta_Grind_nextGoal_x3f___closed__2 = _init_l_Lean_Meta_Grind_nextGoal_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___closed__2);
l_Lean_Meta_Grind_nextGoal_x3f___closed__3 = _init_l_Lean_Meta_Grind_nextGoal_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_nextGoal_x3f___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
