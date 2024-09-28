// Lean compiler output
// Module: Lean.Meta.Tactic.SolveByElim
// Imports: Init.Data.Sum Lean.LabelAttribute Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Backtrack Lean.Meta.Tactic.Constructor Lean.Meta.Tactic.Repeat Lean.Meta.Tactic.Symm Lean.Elab.Term
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_all___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_List_removeAll___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__14;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_occurs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__13;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__15;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__2;
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_backtracking___default;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__6___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SolveByElim_elabContextLemmas___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_intro___default;
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at_Lean_Meta_SolveByElim_solveByElim_run___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lambda__1___closed__1;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at_Lean_MVarId_applyRules___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_labelled(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__10;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at_Lean_Meta_SolveByElim_saturateSymm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__1;
lean_object* l_List_filter___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at_Lean_MVarId_applyRules___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__17;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__4;
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_ApplyRulesConfig_exfalso___default;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__10;
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__22;
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__8;
static lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__5;
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__18;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Meta_repeat_x27Core_go___spec__1(lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_observing_x3f___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__2;
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__19;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__20;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Backtrack_backtrack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object*);
LEAN_EXPORT lean_object* l_List_removeAll___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__5___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lambda__2(lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3;
lean_object* l_Lean_withTraceNode___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__12;
static lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__6;
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_constructor___default;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig(lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__16;
static lean_object* l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_filterMapM___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_removeAll___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__5___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2;
static lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_maxDepth___default;
lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__3;
static lean_object* l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__1;
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__1;
lean_object* l_Lean_exceptEmoji___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_ApplyRulesConfig_symm___default;
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__9;
static lean_object* l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_ofList___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__7;
static lean_object* l_Lean_Meta_SolveByElim_solveByElim___closed__1;
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_applySymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SolveByElim_solveByElim_run___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___boxed(lean_object*);
static lean_object* l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__1;
LEAN_EXPORT lean_object* l_List_filterAuxM___at_Lean_Meta_SolveByElim_applyTactics___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_ApplyRulesConfig_maxDepth___default;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1;
static lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__4;
lean_object* l_List_foldl___at_Array_appendList___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_flatten___rarg(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__11;
lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__17;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SolveByElim_solveByElim_run___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Iterator_head___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at_Lean_Meta_SolveByElim_solveByElim_run___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__13;
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_ApplyRulesConfig_transparency___default;
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lambda__1___closed__1;
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_withTraceNode___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2;
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__1;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___closed__4;
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__19;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__1;
lean_object* l_Lean_MVarId_inferInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__11;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("solveByElim", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__1;
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__2;
x_3 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__6;
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SolveByElim", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__7;
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__9;
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__11;
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__13;
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__14;
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__15;
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__16;
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__17;
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__19;
x_2 = lean_unsigned_to_nat(6u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__4;
x_3 = 0;
x_4 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__20;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at_Lean_Meta_SolveByElim_applyTactics___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_12 = l_Lean_MVarId_inferInstance(x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_free_object(x_1);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_1 = x_11;
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = l_Lean_Exception_isInterrupt(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Exception_isRuntime(x_16);
if (x_19 == 0)
{
lean_free_object(x_12);
lean_dec(x_16);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
else
{
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = l_Lean_Exception_isInterrupt(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_21);
if (x_24 == 0)
{
lean_dec(x_21);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_22;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_26; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_28);
x_30 = l_Lean_MVarId_inferInstance(x_28, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_1 = x_29;
x_7 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_35 = x_30;
} else {
 lean_dec_ref(x_30);
 x_35 = lean_box(0);
}
x_36 = l_Lean_Exception_isInterrupt(x_33);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Exception_isRuntime(x_33);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_33);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_2);
x_1 = x_29;
x_2 = x_38;
x_7 = x_34;
goto _start;
}
else
{
lean_object* x_40; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_35)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_35;
}
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_35)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_35;
}
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" trying to apply: ", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = l_Lean_exceptEmoji___rarg(x_2);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__2;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__4;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_MessageData_ofExpr(x_1);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 5);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_18 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 1);
lean_ctor_set_uint8(x_10, 9, x_1);
x_19 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*6, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*6 + 1, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_MVarId_apply(x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l_List_filterAuxM___at_Lean_Meta_SolveByElim_applyTactics___spec__1(x_21, x_23, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = l_List_reverse___rarg(x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = l_List_reverse___rarg(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_40 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_41 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 1);
x_42 = lean_ctor_get_uint8(x_10, 0);
x_43 = lean_ctor_get_uint8(x_10, 1);
x_44 = lean_ctor_get_uint8(x_10, 2);
x_45 = lean_ctor_get_uint8(x_10, 3);
x_46 = lean_ctor_get_uint8(x_10, 4);
x_47 = lean_ctor_get_uint8(x_10, 5);
x_48 = lean_ctor_get_uint8(x_10, 6);
x_49 = lean_ctor_get_uint8(x_10, 7);
x_50 = lean_ctor_get_uint8(x_10, 8);
x_51 = lean_ctor_get_uint8(x_10, 10);
x_52 = lean_ctor_get_uint8(x_10, 11);
x_53 = lean_ctor_get_uint8(x_10, 12);
lean_dec(x_10);
x_54 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_54, 0, x_42);
lean_ctor_set_uint8(x_54, 1, x_43);
lean_ctor_set_uint8(x_54, 2, x_44);
lean_ctor_set_uint8(x_54, 3, x_45);
lean_ctor_set_uint8(x_54, 4, x_46);
lean_ctor_set_uint8(x_54, 5, x_47);
lean_ctor_set_uint8(x_54, 6, x_48);
lean_ctor_set_uint8(x_54, 7, x_49);
lean_ctor_set_uint8(x_54, 8, x_50);
lean_ctor_set_uint8(x_54, 9, x_1);
lean_ctor_set_uint8(x_54, 10, x_51);
lean_ctor_set_uint8(x_54, 11, x_52);
lean_ctor_set_uint8(x_54, 12, x_53);
x_55 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
lean_ctor_set(x_55, 2, x_12);
lean_ctor_set(x_55, 3, x_13);
lean_ctor_set(x_55, 4, x_14);
lean_ctor_set(x_55, 5, x_15);
lean_ctor_set_uint8(x_55, sizeof(void*)*6, x_40);
lean_ctor_set_uint8(x_55, sizeof(void*)*6 + 1, x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_56 = l_Lean_MVarId_apply(x_2, x_3, x_4, x_55, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_box(0);
x_60 = l_List_filterAuxM___at_Lean_Meta_SolveByElim_applyTactics___spec__1(x_57, x_59, x_5, x_6, x_7, x_8, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
x_64 = l_List_reverse___rarg(x_61);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_68 = x_60;
} else {
 lean_dec_ref(x_60);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = lean_ctor_get(x_56, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_72 = x_56;
} else {
 lean_dec_ref(x_56);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___lambda__1___boxed), 7, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = lean_box(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___lambda__2___boxed), 9, 4);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_3);
x_13 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__4;
x_14 = 1;
x_15 = l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__1;
x_16 = lean_box(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__3___boxed), 10, 5);
lean_closure_set(x_17, 0, x_13);
lean_closure_set(x_17, 1, x_10);
lean_closure_set(x_17, 2, x_12);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_15);
x_18 = l_Lean_observing_x3f___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__5(x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_Iterator_ofList___rarg(x_3, x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___lambda__3___boxed), 9, 3);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Iterator_filterMapM___elambda__1___rarg), 7, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_12);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_box(x_2);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyTactics___lambda__3___boxed), 9, 3);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Iterator_filterMapM___elambda__1___rarg), 7, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SolveByElim_applyTactics___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Meta_SolveByElim_applyTactics___lambda__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Meta_SolveByElim_applyTactics___lambda__3(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyTactics___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_SolveByElim_applyTactics(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Meta_SolveByElim_applyTactics(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Iterator_head___rarg(x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_SolveByElim_applyFirst(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_ApplyRulesConfig_maxDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(50u);
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_SolveByElim_ApplyRulesConfig_transparency___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_SolveByElim_ApplyRulesConfig_symm___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_SolveByElim_ApplyRulesConfig_exfalso___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_maxDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(6u);
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_backtracking___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_intro___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_constructor___default() {
_start:
{
uint8_t x_1; 
x_1 = 1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SolveByElim_SolveByElimConfig_instCoeBacktrackConfig(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_6(x_13, x_3, x_4, x_5, x_6, x_7, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_accept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lambda__1), 8, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_4);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 3);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
lean_ctor_set(x_4, 3, x_13);
return x_1;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_12);
lean_ctor_set(x_3, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
lean_inc(x_20);
lean_dec(x_3);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 2);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lambda__1), 8, 2);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 4, 1);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_27);
x_31 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_21);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 1, x_22);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 2, x_23);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
}
else
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_39 = x_3;
} else {
 lean_dec_ref(x_3);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_4, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_accept___lambda__1), 8, 2);
lean_closure_set(x_44, 0, x_2);
lean_closure_set(x_44, 1, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_45 = x_4;
} else {
 lean_dec_ref(x_4);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 4, 1);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_43);
if (lean_is_scalar(x_39)) {
 x_47 = lean_alloc_ctor(0, 2, 3);
} else {
 x_47 = x_39;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_36);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 1, x_37);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 2, x_38);
x_48 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_32);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 1, x_33);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 2, x_34);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_apply_7(x_10, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = lean_apply_6(x_2, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_List_appendTR___rarg(x_17, x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
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
x_22 = l_List_appendTR___rarg(x_20, x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_14);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
x_28 = l_Lean_Exception_isInterrupt(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_15);
lean_dec(x_26);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_apply_7(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = l_Lean_Exception_isInterrupt(x_40);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Exception_isRuntime(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_apply_7(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_52 = x_45;
} else {
 lean_dec_ref(x_45);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_41);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_40);
lean_ctor_set(x_55, 1, x_41);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lambda__1), 9, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_2);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 3);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
lean_ctor_set(x_4, 1, x_13);
return x_1;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 3, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_12);
lean_ctor_set(x_3, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
lean_inc(x_20);
lean_dec(x_3);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 3);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lambda__1), 9, 2);
lean_closure_set(x_28, 0, x_4);
lean_closure_set(x_28, 1, x_2);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 4, 1);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_27);
x_31 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_21);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 1, x_22);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 2, x_23);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
}
else
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_39 = x_3;
} else {
 lean_dec_ref(x_3);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_4, 3);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc___lambda__1), 9, 2);
lean_closure_set(x_44, 0, x_4);
lean_closure_set(x_44, 1, x_2);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_45 = x_4;
} else {
 lean_dec_ref(x_4);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 4, 1);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_43);
if (lean_is_scalar(x_39)) {
 x_47 = lean_alloc_ctor(0, 2, 3);
} else {
 x_47 = x_39;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_36);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 1, x_37);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 2, x_38);
x_48 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_32);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 1, x_33);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 2, x_34);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Meta_intro1Core(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_intros(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__1;
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_synthInstance(x_8, x_10, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_12, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
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
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__1;
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_mainGoalProc(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Exception_isInterrupt(x_11);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Exception_isRuntime(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_9);
lean_dec(x_11);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_6(x_15, x_3, x_4, x_5, x_6, x_7, x_12);
return x_16;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = l_Lean_Exception_isInterrupt(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isRuntime(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_6(x_21, x_3, x_4, x_5, x_6, x_7, x_18);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lambda__1), 8, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_4);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 3);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
lean_ctor_set(x_4, 3, x_13);
return x_1;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_12);
lean_ctor_set(x_3, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
lean_inc(x_20);
lean_dec(x_3);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 2);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lambda__1), 8, 2);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 4, 1);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_27);
x_31 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_21);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 1, x_22);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 2, x_23);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
}
else
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_39 = x_3;
} else {
 lean_dec_ref(x_3);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_4, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge___lambda__1), 8, 2);
lean_closure_set(x_44, 0, x_2);
lean_closure_set(x_44, 1, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_45 = x_4;
} else {
 lean_dec_ref(x_4);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 4, 1);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_43);
if (lean_is_scalar(x_39)) {
 x_47 = lean_alloc_ctor(0, 2, 3);
} else {
 x_47 = x_39;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_36);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 1, x_37);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 2, x_38);
x_48 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_32);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 1, x_33);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 2, x_34);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_Meta_intro1Core(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__1;
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 2;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_3);
lean_ctor_set_uint8(x_4, 3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lambda__1___closed__1;
x_8 = l_Lean_MVarId_constructor(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
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
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
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
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1;
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_synthInstance(x_8, x_10, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_12, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lambda__1___closed__1;
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lambda__1___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
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
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__1;
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_13 = l_Lean_Expr_mvar___override(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1___boxed), 6, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_11, x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_16);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_23);
x_25 = l_Lean_Expr_mvar___override(x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1___boxed), 6, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_23, x_26, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_2);
x_1 = x_24;
x_2 = x_30;
x_7 = x_29;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_34 = x_27;
} else {
 lean_dec_ref(x_27);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_11 = l_List_mapM_loop___at_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___spec__1(x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_apply_6(x_1, x_12, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__2;
x_19 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_18, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
x_26 = lean_apply_7(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1), 9, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_4);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 3);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
lean_ctor_set(x_4, 1, x_13);
return x_1;
}
else
{
lean_object* x_19; 
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_10);
lean_ctor_set(x_19, 3, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_12);
lean_ctor_set(x_3, 0, x_19);
return x_1;
}
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
lean_inc(x_20);
lean_dec(x_3);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 3);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1), 9, 2);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 4, 1);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_27);
x_31 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_21);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 1, x_22);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 2, x_23);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
}
else
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_37 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_39 = x_3;
} else {
 lean_dec_ref(x_3);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_4, 3);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*4);
lean_inc(x_4);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1), 9, 2);
lean_closure_set(x_44, 0, x_2);
lean_closure_set(x_44, 1, x_4);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 x_45 = x_4;
} else {
 lean_dec_ref(x_4);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 4, 1);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_43);
if (lean_is_scalar(x_39)) {
 x_47 = lean_alloc_ctor(0, 2, 3);
} else {
 x_47 = x_39;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_36);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 1, x_37);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 2, x_38);
x_48 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_32);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 1, x_33);
lean_ctor_set_uint8(x_48, sizeof(void*)*1 + 2, x_34);
return x_48;
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_hasMVar___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lambda__1___closed__1;
lean_inc(x_2);
x_9 = l_List_any___rarg(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lambda__1), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Expr_occurs___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_any___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_List_all___rarg(x_1, x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__2___boxed), 7, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SolveByElim_SolveByElimConfig_requireUsingAll___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_3 == 0)
{
return x_1;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*1 + 2, x_5);
x_6 = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1;
x_7 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_inc(x_8);
lean_dec(x_1);
x_10 = 0;
x_11 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_11, sizeof(void*)*1 + 2, x_10);
x_12 = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1;
x_13 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_11, x_12);
return x_13;
}
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*1 + 1, x_15);
x_16 = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__1;
x_17 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_1, x_16);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1 + 2);
if (x_18 == 0)
{
return x_17;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 2, x_15);
x_20 = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1;
x_21 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_17, x_20);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_24 = lean_ctor_get_uint8(x_17, sizeof(void*)*1 + 1);
lean_inc(x_22);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 2, x_15);
x_26 = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1;
x_27 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_25, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_inc(x_28);
lean_dec(x_1);
x_31 = 0;
x_32 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*1 + 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1 + 2, x_30);
x_33 = l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__1;
x_34 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_32, x_33);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*1 + 2);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
x_38 = lean_ctor_get_uint8(x_34, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_39 = x_34;
} else {
 lean_dec_ref(x_34);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 1, 3);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*1 + 1, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1 + 2, x_31);
x_41 = l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1;
x_42 = l_Lean_Meta_SolveByElim_SolveByElimConfig_withDischarge(x_40, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SolveByElim_elabContextLemmas___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = l_List_reverse___rarg(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_apply_7(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_16);
{
lean_object* _tmp_0 = x_14;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_8 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_free_object(x_1);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
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
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = lean_apply_7(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_2);
x_1 = x_24;
x_2 = x_28;
x_9 = x_27;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_apply_8(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_List_mapM_loop___at_Lean_Meta_SolveByElim_elabContextLemmas___spec__1(x_3, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_List_appendTR___rarg(x_12, x_17);
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
x_21 = l_List_appendTR___rarg(x_12, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_12);
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
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT uint8_t l_Lean_Meta_SolveByElim_elabContextLemmas___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2;
x_3 = l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1;
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
static lean_object* _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = 1;
x_5 = 0;
x_6 = l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3;
x_7 = l_Lean_Meta_SolveByElim_elabContextLemmas___closed__4;
x_8 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
lean_ctor_set(x_8, 5, x_2);
lean_ctor_set(x_8, 6, x_2);
lean_ctor_set(x_8, 7, x_1);
lean_ctor_set(x_8, 8, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*9, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*9 + 1, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*9 + 2, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*9 + 3, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*9 + 4, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*9 + 5, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*9 + 6, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*9 + 7, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*9 + 8, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*9 + 9, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_elabContextLemmas___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_3);
x_11 = l_Lean_Meta_SolveByElim_elabContextLemmas___closed__5;
x_12 = l_Lean_Meta_SolveByElim_elabContextLemmas___closed__6;
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_run_x27___rarg), 8, 3);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_12);
x_14 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_2, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_elabContextLemmas___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_SolveByElim_elabContextLemmas___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyLemmas(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_Meta_SolveByElim_elabContextLemmas(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
x_16 = l_Lean_Meta_SolveByElim_applyTactics(x_14, x_15, x_11, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_applyFirstLemma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_Meta_SolveByElim_elabContextLemmas(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
x_16 = l_Lean_Meta_SolveByElim_applyFirst(x_14, x_15, x_11, x_4, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at_Lean_Meta_SolveByElim_solveByElim_run___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_4 = x_15;
x_5 = x_16;
goto _start;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_19, x_7, x_8, x_9, x_10, x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_21, 0);
lean_dec(x_26);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_21);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_2, x_29);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_19);
x_31 = lean_apply_1(x_1, x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_32 = l_Lean_observing_x3f___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__5(x_31, x_7, x_8, x_9, x_10, x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_free_object(x_4);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_array_push(x_6, x_19);
x_2 = x_30;
x_4 = x_20;
x_6 = x_35;
x_11 = x_34;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_19);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_20);
x_39 = 1;
{
lean_object* _tmp_1 = x_30;
uint8_t _tmp_2 = x_39;
lean_object* _tmp_3 = x_38;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_10 = x_37;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_11 = _tmp_10;
}
goto _start;
}
}
else
{
uint8_t x_41; 
lean_dec(x_30);
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_array_push(x_6, x_19);
x_46 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_45, x_20);
x_47 = l_List_foldl___at_Lean_Meta_repeat_x27Core_go___spec__1(x_46, x_5);
x_48 = lean_box(x_3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_21, 0, x_49);
return x_21;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_dec(x_21);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_2, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_sub(x_2, x_53);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_19);
x_55 = lean_apply_1(x_1, x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_56 = l_Lean_observing_x3f___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__5(x_55, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_free_object(x_4);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_push(x_6, x_19);
x_2 = x_54;
x_4 = x_20;
x_6 = x_59;
x_11 = x_58;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_19);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
lean_dec(x_57);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_20);
x_63 = 1;
{
lean_object* _tmp_1 = x_54;
uint8_t _tmp_2 = x_63;
lean_object* _tmp_3 = x_62;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_10 = x_61;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_11 = _tmp_10;
}
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_54);
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_67 = x_56;
} else {
 lean_dec_ref(x_56);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_array_push(x_6, x_19);
x_70 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_69, x_20);
x_71 = l_List_foldl___at_Lean_Meta_repeat_x27Core_go___spec__1(x_70, x_5);
x_72 = lean_box(x_3);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_50);
return x_74;
}
}
}
else
{
lean_object* x_75; 
lean_free_object(x_4);
lean_dec(x_19);
x_75 = lean_ctor_get(x_21, 1);
lean_inc(x_75);
lean_dec(x_21);
x_4 = x_20;
x_11 = x_75;
goto _start;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_4, 0);
x_78 = lean_ctor_get(x_4, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_4);
x_79 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_77, x_7, x_8, x_9, x_10, x_11);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_eq(x_2, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_83);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_2, x_86);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_77);
x_88 = lean_apply_1(x_1, x_77);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_89 = l_Lean_observing_x3f___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__5(x_88, x_7, x_8, x_9, x_10, x_82);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_array_push(x_6, x_77);
x_2 = x_87;
x_4 = x_78;
x_6 = x_92;
x_11 = x_91;
goto _start;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_77);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_78);
lean_ctor_set(x_96, 1, x_5);
x_97 = 1;
x_2 = x_87;
x_3 = x_97;
x_4 = x_95;
x_5 = x_96;
x_11 = x_94;
goto _start;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_87);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_99 = lean_ctor_get(x_89, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_89, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_101 = x_89;
} else {
 lean_dec_ref(x_89);
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
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_array_push(x_6, x_77);
x_104 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_103, x_78);
x_105 = l_List_foldl___at_Lean_Meta_repeat_x27Core_go___spec__1(x_104, x_5);
x_106 = lean_box(x_3);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
if (lean_is_scalar(x_83)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_83;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_82);
return x_108;
}
}
else
{
lean_object* x_109; 
lean_dec(x_77);
x_109 = lean_ctor_get(x_79, 1);
lean_inc(x_109);
lean_dec(x_79);
x_4 = x_78;
x_11 = x_109;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SolveByElim_solveByElim_run___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_11, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_array_push(x_4, x_11);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_16;
x_9 = x_15;
goto _start;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_9 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__1;
x_2 = lean_array_to_list(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = 0;
x_11 = l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Meta_repeat_x27Core_go___at_Lean_Meta_SolveByElim_solveByElim_run___spec__3(x_1, x_3, x_10, x_2, x_9, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2;
lean_ctor_set(x_14, 1, x_21);
return x_12;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2;
lean_ctor_set(x_14, 1, x_23);
return x_12;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
lean_free_object(x_12);
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SolveByElim_solveByElim_run___spec__4(x_17, x_24, x_25, x_11, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_17);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_array_to_list(x_28);
lean_ctor_set(x_14, 1, x_29);
lean_ctor_set(x_26, 0, x_14);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_array_to_list(x_30);
lean_ctor_set(x_14, 1, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_12, 1);
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_array_get_size(x_36);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_lt(x_38, x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_12, 0, x_41);
return x_12;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_37, x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_12, 0, x_44);
return x_12;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_12);
x_45 = 0;
x_46 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_47 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SolveByElim_solveByElim_run___spec__4(x_36, x_45, x_46, x_11, x_4, x_5, x_6, x_7, x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_36);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
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
x_51 = lean_array_to_list(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_35);
lean_ctor_set(x_52, 1, x_51);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_54 = lean_ctor_get(x_12, 0);
x_55 = lean_ctor_get(x_12, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_12);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_58 = x_54;
} else {
 lean_dec_ref(x_54);
 x_58 = lean_box(0);
}
x_59 = lean_array_get_size(x_57);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_lt(x_60, x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2;
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_59, x_59);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2;
if (lean_is_scalar(x_58)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_58;
}
lean_ctor_set(x_67, 0, x_56);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_55);
return x_68;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = 0;
x_70 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_71 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SolveByElim_solveByElim_run___spec__4(x_57, x_69, x_70, x_11, x_4, x_5, x_6, x_7, x_55);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_57);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_array_to_list(x_72);
if (lean_is_scalar(x_58)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_58;
}
lean_ctor_set(x_76, 0, x_56);
lean_ctor_set(x_76, 1, x_75);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_12);
if (x_78 == 0)
{
return x_12;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_12, 0);
x_80 = lean_ctor_get(x_12, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_12);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("repeat1' made no progress", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__2;
x_15 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__1(x_14, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyFirstLemma), 9, 3);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1(x_11, x_4, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_applyLemmas), 9, 3);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
x_19 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__4;
x_20 = l_Lean_Meta_Tactic_Backtrack_backtrack(x_17, x_19, x_18, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_repeat_x27Core_go___at_Lean_Meta_SolveByElim_solveByElim_run___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_repeat_x27Core_go___at_Lean_Meta_SolveByElim_solveByElim_run___spec__3(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SolveByElim_solveByElim_run___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SolveByElim_solveByElim_run___spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⏮️ starting over using `exfalso`", 36, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_MVarId_exfalso(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_SolveByElim_solveByElim_run(x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_solveByElim___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_SolveByElim_SolveByElimConfig_processOptions(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_SolveByElim_solveByElim_run(x_2, x_3, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_Lean_Exception_isInterrupt(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Exception_isRuntime(x_13);
if (x_16 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*2 + 2);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_11);
lean_dec(x_13);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_solveByElim___lambda__2), 9, 4);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_10);
x_22 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__4;
x_23 = l_Lean_Meta_SolveByElim_solveByElim___closed__1;
x_24 = 1;
x_25 = l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__1;
x_26 = l_Lean_withTraceNode___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__3(x_22, x_23, x_21, x_24, x_25, x_5, x_6, x_7, x_8, x_14);
return x_26;
}
}
else
{
lean_dec(x_17);
lean_dec(x_10);
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
}
else
{
lean_dec(x_10);
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
else
{
lean_dec(x_10);
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
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = l_Lean_Exception_isInterrupt(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_27);
if (x_30 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_10, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*2 + 2);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_27);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
lean_dec(x_4);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_solveByElim___lambda__2), 9, 4);
lean_closure_set(x_37, 0, x_36);
lean_closure_set(x_37, 1, x_2);
lean_closure_set(x_37, 2, x_3);
lean_closure_set(x_37, 3, x_10);
x_38 = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__4;
x_39 = l_Lean_Meta_SolveByElim_solveByElim___closed__1;
x_40 = 1;
x_41 = l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__1;
x_42 = l_Lean_withTraceNode___at___private_Lean_Meta_Tactic_Backtrack_0__Lean_Meta_Tactic_Backtrack_Backtrack_run___spec__3(x_38, x_39, x_37, x_40, x_41, x_5, x_6, x_7, x_8, x_28);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_27);
lean_ctor_set(x_43, 1, x_28);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_28);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_28);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_solveByElim___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SolveByElim_solveByElim___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_filterMapM_loop___at_Lean_Meta_SolveByElim_saturateSymm___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Expr_applySymm(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_12;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_free_object(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
if (x_21 == 0)
{
lean_free_object(x_13);
lean_dec(x_18);
x_1 = x_12;
x_7 = x_19;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
else
{
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = l_Lean_Exception_isInterrupt(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_23);
if (x_26 == 0)
{
lean_dec(x_23);
x_1 = x_12;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Expr_applySymm(x_30, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_2);
x_1 = x_31;
x_2 = x_35;
x_7 = x_34;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
x_40 = l_Lean_Exception_isInterrupt(x_37);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Exception_isRuntime(x_37);
if (x_41 == 0)
{
lean_dec(x_39);
lean_dec(x_37);
x_1 = x_31;
x_7 = x_38;
goto _start;
}
else
{
lean_object* x_43; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_39;
}
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
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
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
lean_inc(x_2);
x_10 = l_List_filterMapM_loop___at_Lean_Meta_SolveByElim_saturateSymm___spec__1(x_2, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_List_appendTR___rarg(x_2, x_12);
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
x_16 = l_List_appendTR___rarg(x_2, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_saturateSymm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Meta_SolveByElim_saturateSymm(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_3, x_5);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 0);
lean_dec(x_19);
lean_inc(x_18);
x_20 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3(x_1, x_16, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_20, 0, x_6);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_29);
lean_ctor_set(x_6, 0, x_2);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_5 = x_31;
x_13 = x_28;
goto _start;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_dec(x_6);
lean_inc(x_33);
x_34 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3(x_1, x_16, x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
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
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
lean_dec(x_33);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
lean_dec(x_35);
lean_inc(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_42);
x_44 = 1;
x_45 = lean_usize_add(x_5, x_44);
x_5 = x_45;
x_6 = x_43;
x_13 = x_41;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec(x_5);
lean_inc(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
x_5 = x_22;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = l_Lean_LocalDecl_isImplementationDetail(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_31 = l_Lean_LocalDecl_toExpr(x_29);
lean_dec(x_29);
x_32 = lean_array_push(x_27, x_31);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_32);
lean_ctor_set(x_5, 0, x_1);
x_33 = 1;
x_34 = lean_usize_add(x_4, x_33);
x_4 = x_34;
goto _start;
}
else
{
size_t x_36; size_t x_37; 
lean_dec(x_29);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
x_4 = x_37;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
lean_dec(x_5);
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = l_Lean_LocalDecl_isImplementationDetail(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_42 = l_Lean_LocalDecl_toExpr(x_40);
lean_dec(x_40);
x_43 = lean_array_push(x_39, x_42);
lean_inc(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_4, x_45);
x_4 = x_46;
x_5 = x_44;
goto _start;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; 
lean_dec(x_40);
lean_inc(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_39);
x_49 = 1;
x_50 = lean_usize_add(x_4, x_49);
x_4 = x_50;
x_5 = x_48;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_array_size(x_11);
x_15 = 0;
x_16 = l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__4(x_1, x_12, x_11, x_14, x_15, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3___lambda__1(x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
x_32 = lean_array_size(x_29);
x_33 = 0;
x_34 = l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__5(x_30, x_29, x_32, x_33, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3___lambda__1(x_38, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_35);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_34, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_43);
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_dec(x_5);
lean_inc(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
x_5 = x_22;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_5, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = l_Lean_LocalDecl_isImplementationDetail(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
x_31 = l_Lean_LocalDecl_toExpr(x_29);
lean_dec(x_29);
x_32 = lean_array_push(x_27, x_31);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_32);
lean_ctor_set(x_5, 0, x_1);
x_33 = 1;
x_34 = lean_usize_add(x_4, x_33);
x_4 = x_34;
goto _start;
}
else
{
size_t x_36; size_t x_37; 
lean_dec(x_29);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_36 = 1;
x_37 = lean_usize_add(x_4, x_36);
x_4 = x_37;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
lean_dec(x_5);
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = l_Lean_LocalDecl_isImplementationDetail(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_42 = l_Lean_LocalDecl_toExpr(x_40);
lean_dec(x_40);
x_43 = lean_array_push(x_39, x_42);
lean_inc(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_4, x_45);
x_4 = x_46;
x_5 = x_44;
goto _start;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; 
lean_dec(x_40);
lean_inc(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_39);
x_49 = 1;
x_50 = lean_usize_add(x_4, x_49);
x_4 = x_50;
x_5 = x_48;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_11 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3(x_2, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
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
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_size(x_21);
x_25 = 0;
x_26 = l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__6(x_22, x_21, x_24, x_25, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_26, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at_Lean_MVarId_applyRules___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_8, 1);
x_10 = l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__1;
x_11 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_getLocalHyps___at_Lean_MVarId_applyRules___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2 + 1);
x_15 = lean_array_to_list(x_11);
x_16 = l_Lean_Meta_SolveByElim_saturateSymm(x_14, x_15, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_box(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_applyRules___lambda__1___boxed), 9, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_13);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_SolveByElim_solveByElim(x_1, x_2, x_11, x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
lean_inc(x_17);
lean_dec(x_1);
x_20 = 0;
x_21 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 1, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*1 + 2, x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_SolveByElim_solveByElim(x_21, x_2, x_11, x_23, x_5, x_6, x_7, x_8, x_9);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__4(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__5(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_forInAux___at_Lean_MVarId_applyRules___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_MVarId_applyRules___spec__6(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at_Lean_MVarId_applyRules___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at_Lean_MVarId_applyRules___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getLocalHyps___at_Lean_MVarId_applyRules___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_MVarId_applyRules___lambda__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_applyRules___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_MVarId_applyRules(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = 1;
x_11 = l_Lean_Elab_Term_elabTerm(x_1, x_9, x_10, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27), 8, 1);
lean_closure_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27), 8, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
x_15 = l_Lean_labelled(x_14, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_13, x_2, x_16);
x_2 = x_19;
x_3 = x_20;
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_closure((void*)(l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3___lambda__1___boxed), 8, 1);
lean_closure_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_closure((void*)(l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3___lambda__1___boxed), 8, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = l_List_reverse___rarg(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_16);
{
lean_object* _tmp_0 = x_14;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_8 = x_17;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_free_object(x_1);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
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
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Meta_SolveByElim_mkAssumptionSet_elab_x27(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_2);
x_1 = x_24;
x_2 = x_28;
x_9 = x_27;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_expr_eqv(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_List_removeAll___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__5___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_List_elem___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__6(x_2, x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_List_removeAll___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__5___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_filter___rarg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
if (x_3 == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_13 = x_30;
goto block_29;
}
else
{
if (x_4 == 0)
{
lean_object* x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_12);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_box(0);
x_13 = x_32;
goto block_29;
}
}
block_29:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
x_14 = l_Lean_getLocalHyps___at_Lean_MVarId_applyRules___spec__1(x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_List_mapM_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__4(x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 1);
x_22 = lean_array_to_list(x_15);
x_23 = l_List_removeAll___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__5(x_22, x_18);
x_24 = l_Lean_Meta_SolveByElim_saturateSymm(x_21, x_23, x_8, x_9, x_10, x_11, x_19);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(x_3);
x_13 = lean_box(x_4);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__1___boxed), 12, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rfl", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__6;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrFun", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__11;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__16;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("It doesn't make sense to remove local hypotheses when using `only` without `*`.", 79, 79);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 5);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_9, 10);
lean_inc(x_15);
x_16 = lean_st_ref_get(x_10, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_environment_main_module(x_20);
x_22 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__3;
lean_inc(x_15);
x_23 = l_Lean_addMacroScope(x_21, x_22, x_15);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__2;
x_26 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__5;
lean_inc(x_14);
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_st_ref_get(x_10, x_19);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_environment_main_module(x_32);
x_34 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__8;
lean_inc(x_15);
x_35 = l_Lean_addMacroScope(x_33, x_34, x_15);
x_36 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__7;
x_37 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__10;
lean_inc(x_14);
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_st_ref_get(x_10, x_31);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_environment_main_module(x_43);
x_45 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__13;
lean_inc(x_15);
x_46 = l_Lean_addMacroScope(x_44, x_45, x_15);
x_47 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__12;
x_48 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__15;
lean_inc(x_14);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_14);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_st_ref_get(x_10, x_42);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_environment_main_module(x_54);
x_56 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18;
x_57 = l_Lean_addMacroScope(x_55, x_56, x_15);
x_58 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__17;
x_59 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__20;
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_14);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 1, x_24);
lean_ctor_set(x_50, 0, x_60);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 1, x_50);
lean_ctor_set(x_39, 0, x_49);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_39);
lean_ctor_set(x_28, 0, x_38);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_27);
x_61 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_16, x_24);
x_62 = lean_array_size(x_1);
x_63 = 0;
x_64 = l_Array_mapMUnsafe_map___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__2(x_62, x_63, x_1, x_7, x_8, x_9, x_10, x_53);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Array_flatten___rarg(x_65);
lean_dec(x_65);
x_68 = lean_array_to_list(x_67);
x_69 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3(x_68, x_24);
x_70 = l_List_isEmpty___rarg(x_2);
if (x_3 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_5, x_24);
x_86 = l_List_appendTR___rarg(x_85, x_69);
x_87 = l_List_appendTR___rarg(x_86, x_61);
x_71 = x_87;
goto block_84;
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_61);
x_88 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_5, x_24);
x_89 = l_List_appendTR___rarg(x_88, x_69);
x_71 = x_89;
goto block_84;
}
block_84:
{
if (x_70 == 0)
{
if (x_3 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(0);
x_73 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_71, x_72, x_7, x_8, x_9, x_10, x_66);
lean_dec(x_9);
return x_73;
}
else
{
if (x_4 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_71);
lean_dec(x_2);
x_74 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__22;
x_75 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_74, x_7, x_8, x_9, x_10, x_66);
lean_dec(x_9);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_box(0);
x_81 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_71, x_80, x_7, x_8, x_9, x_10, x_66);
lean_dec(x_9);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_box(0);
x_83 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_71, x_82, x_7, x_8, x_9, x_10, x_66);
lean_dec(x_9);
return x_83;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_61);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_64);
if (x_90 == 0)
{
return x_64;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_64, 0);
x_92 = lean_ctor_get(x_64, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_64);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; lean_object* x_107; 
x_94 = lean_ctor_get(x_50, 0);
x_95 = lean_ctor_get(x_50, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_50);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_environment_main_module(x_96);
x_98 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18;
x_99 = l_Lean_addMacroScope(x_97, x_98, x_15);
x_100 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__17;
x_101 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__20;
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_14);
lean_ctor_set(x_102, 1, x_100);
lean_ctor_set(x_102, 2, x_99);
lean_ctor_set(x_102, 3, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_24);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 1, x_103);
lean_ctor_set(x_39, 0, x_49);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_39);
lean_ctor_set(x_28, 0, x_38);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_27);
x_104 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_16, x_24);
x_105 = lean_array_size(x_1);
x_106 = 0;
x_107 = l_Array_mapMUnsafe_map___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__2(x_105, x_106, x_1, x_7, x_8, x_9, x_10, x_95);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Array_flatten___rarg(x_108);
lean_dec(x_108);
x_111 = lean_array_to_list(x_110);
x_112 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3(x_111, x_24);
x_113 = l_List_isEmpty___rarg(x_2);
if (x_3 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_5, x_24);
x_129 = l_List_appendTR___rarg(x_128, x_112);
x_130 = l_List_appendTR___rarg(x_129, x_104);
x_114 = x_130;
goto block_127;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_104);
x_131 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_5, x_24);
x_132 = l_List_appendTR___rarg(x_131, x_112);
x_114 = x_132;
goto block_127;
}
block_127:
{
if (x_113 == 0)
{
if (x_3 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_box(0);
x_116 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_114, x_115, x_7, x_8, x_9, x_10, x_109);
lean_dec(x_9);
return x_116;
}
else
{
if (x_4 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_114);
lean_dec(x_2);
x_117 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__22;
x_118 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_117, x_7, x_8, x_9, x_10, x_109);
lean_dec(x_9);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_box(0);
x_124 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_114, x_123, x_7, x_8, x_9, x_10, x_109);
lean_dec(x_9);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_box(0);
x_126 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_114, x_125, x_7, x_8, x_9, x_10, x_109);
lean_dec(x_9);
return x_126;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_104);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_133 = lean_ctor_get(x_107, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_107, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_135 = x_107;
} else {
 lean_dec_ref(x_107);
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
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; size_t x_160; size_t x_161; lean_object* x_162; 
x_137 = lean_ctor_get(x_39, 0);
x_138 = lean_ctor_get(x_39, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_39);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_environment_main_module(x_139);
x_141 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__13;
lean_inc(x_15);
x_142 = l_Lean_addMacroScope(x_140, x_141, x_15);
x_143 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__12;
x_144 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__15;
lean_inc(x_14);
x_145 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_145, 0, x_14);
lean_ctor_set(x_145, 1, x_143);
lean_ctor_set(x_145, 2, x_142);
lean_ctor_set(x_145, 3, x_144);
x_146 = lean_st_ref_get(x_10, x_138);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_environment_main_module(x_150);
x_152 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18;
x_153 = l_Lean_addMacroScope(x_151, x_152, x_15);
x_154 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__17;
x_155 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__20;
x_156 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_156, 0, x_14);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_153);
lean_ctor_set(x_156, 3, x_155);
if (lean_is_scalar(x_149)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_149;
 lean_ctor_set_tag(x_157, 1);
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_24);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_145);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_158);
lean_ctor_set(x_28, 0, x_38);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_27);
x_159 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_16, x_24);
x_160 = lean_array_size(x_1);
x_161 = 0;
x_162 = l_Array_mapMUnsafe_map___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__2(x_160, x_161, x_1, x_7, x_8, x_9, x_10, x_148);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Array_flatten___rarg(x_163);
lean_dec(x_163);
x_166 = lean_array_to_list(x_165);
x_167 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3(x_166, x_24);
x_168 = l_List_isEmpty___rarg(x_2);
if (x_3 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_5, x_24);
x_184 = l_List_appendTR___rarg(x_183, x_167);
x_185 = l_List_appendTR___rarg(x_184, x_159);
x_169 = x_185;
goto block_182;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_159);
x_186 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_5, x_24);
x_187 = l_List_appendTR___rarg(x_186, x_167);
x_169 = x_187;
goto block_182;
}
block_182:
{
if (x_168 == 0)
{
if (x_3 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_box(0);
x_171 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_169, x_170, x_7, x_8, x_9, x_10, x_164);
lean_dec(x_9);
return x_171;
}
else
{
if (x_4 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_169);
lean_dec(x_2);
x_172 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__22;
x_173 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_172, x_7, x_8, x_9, x_10, x_164);
lean_dec(x_9);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
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
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_box(0);
x_179 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_169, x_178, x_7, x_8, x_9, x_10, x_164);
lean_dec(x_9);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_box(0);
x_181 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_169, x_180, x_7, x_8, x_9, x_10, x_164);
lean_dec(x_9);
return x_181;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_159);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_188 = lean_ctor_get(x_162, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_162, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_190 = x_162;
} else {
 lean_dec_ref(x_162);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; size_t x_227; size_t x_228; lean_object* x_229; 
x_192 = lean_ctor_get(x_28, 0);
x_193 = lean_ctor_get(x_28, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_28);
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_environment_main_module(x_194);
x_196 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__8;
lean_inc(x_15);
x_197 = l_Lean_addMacroScope(x_195, x_196, x_15);
x_198 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__7;
x_199 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__10;
lean_inc(x_14);
x_200 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_200, 0, x_14);
lean_ctor_set(x_200, 1, x_198);
lean_ctor_set(x_200, 2, x_197);
lean_ctor_set(x_200, 3, x_199);
x_201 = lean_st_ref_get(x_10, x_193);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_204 = x_201;
} else {
 lean_dec_ref(x_201);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_202, 0);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_environment_main_module(x_205);
x_207 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__13;
lean_inc(x_15);
x_208 = l_Lean_addMacroScope(x_206, x_207, x_15);
x_209 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__12;
x_210 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__15;
lean_inc(x_14);
x_211 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_211, 0, x_14);
lean_ctor_set(x_211, 1, x_209);
lean_ctor_set(x_211, 2, x_208);
lean_ctor_set(x_211, 3, x_210);
x_212 = lean_st_ref_get(x_10, x_203);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_213, 0);
lean_inc(x_216);
lean_dec(x_213);
x_217 = lean_environment_main_module(x_216);
x_218 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18;
x_219 = l_Lean_addMacroScope(x_217, x_218, x_15);
x_220 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__17;
x_221 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__20;
x_222 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_222, 0, x_14);
lean_ctor_set(x_222, 1, x_220);
lean_ctor_set(x_222, 2, x_219);
lean_ctor_set(x_222, 3, x_221);
if (lean_is_scalar(x_215)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_215;
 lean_ctor_set_tag(x_223, 1);
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_24);
if (lean_is_scalar(x_204)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_204;
 lean_ctor_set_tag(x_224, 1);
}
lean_ctor_set(x_224, 0, x_211);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_200);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_225);
lean_ctor_set(x_16, 0, x_27);
x_226 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_16, x_24);
x_227 = lean_array_size(x_1);
x_228 = 0;
x_229 = l_Array_mapMUnsafe_map___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__2(x_227, x_228, x_1, x_7, x_8, x_9, x_10, x_214);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = l_Array_flatten___rarg(x_230);
lean_dec(x_230);
x_233 = lean_array_to_list(x_232);
x_234 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3(x_233, x_24);
x_235 = l_List_isEmpty___rarg(x_2);
if (x_3 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_5, x_24);
x_251 = l_List_appendTR___rarg(x_250, x_234);
x_252 = l_List_appendTR___rarg(x_251, x_226);
x_236 = x_252;
goto block_249;
}
else
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_226);
x_253 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_5, x_24);
x_254 = l_List_appendTR___rarg(x_253, x_234);
x_236 = x_254;
goto block_249;
}
block_249:
{
if (x_235 == 0)
{
if (x_3 == 0)
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_box(0);
x_238 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_236, x_237, x_7, x_8, x_9, x_10, x_231);
lean_dec(x_9);
return x_238;
}
else
{
if (x_4 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_236);
lean_dec(x_2);
x_239 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__22;
x_240 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_239, x_7, x_8, x_9, x_10, x_231);
lean_dec(x_9);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
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
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_box(0);
x_246 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_236, x_245, x_7, x_8, x_9, x_10, x_231);
lean_dec(x_9);
return x_246;
}
}
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_box(0);
x_248 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_24, x_3, x_4, x_236, x_247, x_7, x_8, x_9, x_10, x_231);
lean_dec(x_9);
return x_248;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_226);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_255 = lean_ctor_get(x_229, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_229, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_257 = x_229;
} else {
 lean_dec_ref(x_229);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; size_t x_307; size_t x_308; lean_object* x_309; 
x_259 = lean_ctor_get(x_16, 0);
x_260 = lean_ctor_get(x_16, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_16);
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_environment_main_module(x_261);
x_263 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__3;
lean_inc(x_15);
x_264 = l_Lean_addMacroScope(x_262, x_263, x_15);
x_265 = lean_box(0);
x_266 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__2;
x_267 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__5;
lean_inc(x_14);
x_268 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_268, 0, x_14);
lean_ctor_set(x_268, 1, x_266);
lean_ctor_set(x_268, 2, x_264);
lean_ctor_set(x_268, 3, x_267);
x_269 = lean_st_ref_get(x_10, x_260);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_272 = x_269;
} else {
 lean_dec_ref(x_269);
 x_272 = lean_box(0);
}
x_273 = lean_ctor_get(x_270, 0);
lean_inc(x_273);
lean_dec(x_270);
x_274 = lean_environment_main_module(x_273);
x_275 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__8;
lean_inc(x_15);
x_276 = l_Lean_addMacroScope(x_274, x_275, x_15);
x_277 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__7;
x_278 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__10;
lean_inc(x_14);
x_279 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_279, 0, x_14);
lean_ctor_set(x_279, 1, x_277);
lean_ctor_set(x_279, 2, x_276);
lean_ctor_set(x_279, 3, x_278);
x_280 = lean_st_ref_get(x_10, x_271);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_283 = x_280;
} else {
 lean_dec_ref(x_280);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
lean_dec(x_281);
x_285 = lean_environment_main_module(x_284);
x_286 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__13;
lean_inc(x_15);
x_287 = l_Lean_addMacroScope(x_285, x_286, x_15);
x_288 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__12;
x_289 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__15;
lean_inc(x_14);
x_290 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_290, 0, x_14);
lean_ctor_set(x_290, 1, x_288);
lean_ctor_set(x_290, 2, x_287);
lean_ctor_set(x_290, 3, x_289);
x_291 = lean_st_ref_get(x_10, x_282);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_294 = x_291;
} else {
 lean_dec_ref(x_291);
 x_294 = lean_box(0);
}
x_295 = lean_ctor_get(x_292, 0);
lean_inc(x_295);
lean_dec(x_292);
x_296 = lean_environment_main_module(x_295);
x_297 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18;
x_298 = l_Lean_addMacroScope(x_296, x_297, x_15);
x_299 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__17;
x_300 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__20;
x_301 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_301, 0, x_14);
lean_ctor_set(x_301, 1, x_299);
lean_ctor_set(x_301, 2, x_298);
lean_ctor_set(x_301, 3, x_300);
if (lean_is_scalar(x_294)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_294;
 lean_ctor_set_tag(x_302, 1);
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_265);
if (lean_is_scalar(x_283)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_283;
 lean_ctor_set_tag(x_303, 1);
}
lean_ctor_set(x_303, 0, x_290);
lean_ctor_set(x_303, 1, x_302);
if (lean_is_scalar(x_272)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_272;
 lean_ctor_set_tag(x_304, 1);
}
lean_ctor_set(x_304, 0, x_279);
lean_ctor_set(x_304, 1, x_303);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_268);
lean_ctor_set(x_305, 1, x_304);
x_306 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_305, x_265);
x_307 = lean_array_size(x_1);
x_308 = 0;
x_309 = l_Array_mapMUnsafe_map___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__2(x_307, x_308, x_1, x_7, x_8, x_9, x_10, x_293);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = l_Array_flatten___rarg(x_310);
lean_dec(x_310);
x_313 = lean_array_to_list(x_312);
x_314 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3(x_313, x_265);
x_315 = l_List_isEmpty___rarg(x_2);
if (x_3 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_5, x_265);
x_331 = l_List_appendTR___rarg(x_330, x_314);
x_332 = l_List_appendTR___rarg(x_331, x_306);
x_316 = x_332;
goto block_329;
}
else
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_306);
x_333 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__1(x_5, x_265);
x_334 = l_List_appendTR___rarg(x_333, x_314);
x_316 = x_334;
goto block_329;
}
block_329:
{
if (x_315 == 0)
{
if (x_3 == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_box(0);
x_318 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_265, x_3, x_4, x_316, x_317, x_7, x_8, x_9, x_10, x_311);
lean_dec(x_9);
return x_318;
}
else
{
if (x_4 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_316);
lean_dec(x_2);
x_319 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__22;
x_320 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_319, x_7, x_8, x_9, x_10, x_311);
lean_dec(x_9);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_323 = x_320;
} else {
 lean_dec_ref(x_320);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
else
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_box(0);
x_326 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_265, x_3, x_4, x_316, x_325, x_7, x_8, x_9, x_10, x_311);
lean_dec(x_9);
return x_326;
}
}
}
else
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_box(0);
x_328 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_2, x_265, x_3, x_4, x_316, x_327, x_7, x_8, x_9, x_10, x_311);
lean_dec(x_9);
return x_328;
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_306);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
x_335 = lean_ctor_get(x_309, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_309, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_337 = x_309;
} else {
 lean_dec_ref(x_309);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("It doesn't make sense to use `*` without `only`.", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3(x_5, x_4, x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2;
x_14 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3(x_5, x_4, x_1, x_2, x_3, x_19, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__2(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapTR_loop___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_removeAll___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_removeAll___at_Lean_Meta_SolveByElim_mkAssumptionSet___spec__5___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__2(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SolveByElim_mkAssumptionSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_SolveByElim_mkAssumptionSet(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
lean_object* initialize_Init_Data_Sum(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LabelAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Backtrack(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Repeat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Symm(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_SolveByElim(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Sum(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LabelAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Backtrack(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Constructor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Repeat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Symm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__1 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__1);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__2 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__2();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__2);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__3 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__3();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__3);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__4 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__4();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__4);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__5 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__5();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__5);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__6 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__6();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__6);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__7 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__7();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__7);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__8 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__8();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__8);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__9 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__9();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__9);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__10 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__10();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__10);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__11 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__11();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__11);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__12 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__12();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__12);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__13 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__13();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__13);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__14 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__14();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__14);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__15 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__15();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__15);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__16 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__16();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__16);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__17 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__17();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__17);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__18 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__18();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__18);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__19 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__19();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__19);
l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__20 = _init_l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__20();
lean_mark_persistent(l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6____closed__20);
res = l_Lean_Meta_SolveByElim_initFn____x40_Lean_Meta_Tactic_SolveByElim___hyg_6_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__1 = _init_l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__1);
l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__2 = _init_l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__2);
l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__3 = _init_l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__3);
l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__4 = _init_l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_SolveByElim_applyTactics___lambda__1___closed__4);
l_Lean_Meta_SolveByElim_ApplyRulesConfig_maxDepth___default = _init_l_Lean_Meta_SolveByElim_ApplyRulesConfig_maxDepth___default();
lean_mark_persistent(l_Lean_Meta_SolveByElim_ApplyRulesConfig_maxDepth___default);
l_Lean_Meta_SolveByElim_ApplyRulesConfig_transparency___default = _init_l_Lean_Meta_SolveByElim_ApplyRulesConfig_transparency___default();
l_Lean_Meta_SolveByElim_ApplyRulesConfig_symm___default = _init_l_Lean_Meta_SolveByElim_ApplyRulesConfig_symm___default();
l_Lean_Meta_SolveByElim_ApplyRulesConfig_exfalso___default = _init_l_Lean_Meta_SolveByElim_ApplyRulesConfig_exfalso___default();
l_Lean_Meta_SolveByElim_SolveByElimConfig_maxDepth___default = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_maxDepth___default();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_maxDepth___default);
l_Lean_Meta_SolveByElim_SolveByElimConfig_backtracking___default = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_backtracking___default();
l_Lean_Meta_SolveByElim_SolveByElimConfig_intro___default = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_intro___default();
l_Lean_Meta_SolveByElim_SolveByElimConfig_constructor___default = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_constructor___default();
l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__1 = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_intros___closed__1);
l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__1 = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstance___closed__1);
l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__1 = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_introsAfter___closed__1);
l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lambda__1___closed__1 = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___lambda__1___closed__1);
l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1 = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_constructorAfter___closed__1);
l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lambda__1___closed__1 = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___lambda__1___closed__1);
l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__1 = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_synthInstanceAfter___closed__1);
l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__1 = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__1);
l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__2 = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_testPartialSolutions___lambda__1___closed__2);
l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lambda__1___closed__1 = _init_l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_SolveByElimConfig_testSolutions___lambda__1___closed__1);
l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1 = _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__1);
l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2 = _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2();
lean_mark_persistent(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__2);
l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3 = _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3();
lean_mark_persistent(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__3);
l_Lean_Meta_SolveByElim_elabContextLemmas___closed__4 = _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__4();
lean_mark_persistent(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__4);
l_Lean_Meta_SolveByElim_elabContextLemmas___closed__5 = _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__5();
lean_mark_persistent(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__5);
l_Lean_Meta_SolveByElim_elabContextLemmas___closed__6 = _init_l_Lean_Meta_SolveByElim_elabContextLemmas___closed__6();
lean_mark_persistent(l_Lean_Meta_SolveByElim_elabContextLemmas___closed__6);
l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__1 = _init_l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__1();
lean_mark_persistent(l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__1);
l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2 = _init_l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2();
lean_mark_persistent(l_Lean_Meta_repeat_x27Core___at_Lean_Meta_SolveByElim_solveByElim_run___spec__2___closed__2);
l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__1 = _init_l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__1);
l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__2 = _init_l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_repeat1_x27___at_Lean_Meta_SolveByElim_solveByElim_run___spec__1___closed__2);
l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__1 = _init_l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__1);
l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__2 = _init_l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_SolveByElim_solveByElim___lambda__1___closed__2);
l_Lean_Meta_SolveByElim_solveByElim___closed__1 = _init_l_Lean_Meta_SolveByElim_solveByElim___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_solveByElim___closed__1);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__1 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__1);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__2 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__2);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__3 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__3);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__4 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__4);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__5 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__5);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__6 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__6);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__7 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__7);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__8 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__8);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__9 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__9);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__10 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__10);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__11 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__11);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__12 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__12();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__12);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__13 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__13();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__13);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__14 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__14();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__14);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__15 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__15();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__15);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__16 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__16();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__16);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__17 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__17();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__17);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__18);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__19 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__19();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__19);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__20 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__20();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__20);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__21 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__21();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__21);
l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__22 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__22();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___lambda__3___closed__22);
l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__1);
l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2 = _init_l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2();
lean_mark_persistent(l_Lean_Meta_SolveByElim_mkAssumptionSet___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
