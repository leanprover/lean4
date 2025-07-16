// Lean compiler output
// Module: Lean.Elab.Tactic.ElabTerm
// Imports: Lean.Meta.Tactic.Constructor Lean.Meta.Tactic.Assert Lean.Meta.Tactic.AuxLemma Lean.Meta.Tactic.Cleanup Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Rename Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Config Lean.Elab.SyntheticMVars
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
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTermForApply___closed__0;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1;
uint8_t l_Lean_MetavarKind_isNatural(uint8_t);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__19;
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__7;
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__3;
static lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__10;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__23;
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__36;
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__37;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1(lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__16;
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__2;
lean_object* l_Lean_Elab_Term_isLetRecAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__44;
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6;
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0;
lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3;
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___closed__0;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__9;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2;
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__32;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__30;
static lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4;
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__0;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__13;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__28;
static lean_object* l_Lean_Elab_Tactic_evalRefine___closed__2;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__9;
lean_object* l_Lean_MVarId_getKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_filterOldMVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__38;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__6;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1;
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__47;
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__27;
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__12;
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__42;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__0;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1;
lean_object* l_Lean_Elab_Tactic_withoutRecover___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__43;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__24;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__20;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__50;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__21;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6;
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__4;
lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_mkModuleData_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2;
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__6;
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_checked_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__16;
lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__27;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__33;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__17;
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed__const__1;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__17;
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__26;
static lean_object* l_Lean_Elab_Tactic_evalRename___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___closed__0;
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0;
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__26;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_filterOldMVars_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__3;
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6;
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__1;
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__55;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__22;
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3(lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__57;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__54;
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__51;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApply___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3(lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__18;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__53;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainTag___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doElab___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1;
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__23;
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_evalRefine___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__11;
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__3;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__13;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_popMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__49;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApply___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__45;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__15;
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__0;
uint8_t l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__41;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__46;
static lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1;
static uint64_t l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__40;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__8;
lean_object* l_Lean_Elab_Tactic_pushGoal___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__11;
static lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__48;
static lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4;
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_getFVarIds_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2;
lean_object* l_Lean_isDiagnosticsEnabled___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_getFVarIds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__1;
lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at___Lean_Elab_Tactic_evalTactic_eval_spec__7___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0;
lean_object* l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__6;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__25;
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___closed__0;
static lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8;
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__34;
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28;
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__52;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__35;
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__22;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_;
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Name_isMetaprogramming_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__14;
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3(lean_object*);
static uint64_t l_Lean_Elab_Tactic_evalWithReducible___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5;
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__6;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__7;
lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5;
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__7;
static lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___boxed(lean_object**);
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__25;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Term_getLevelNames___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__5;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0;
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__29;
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__0;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4;
lean_object* l_Lean_mkAuxDeclName___at___Lean_Elab_Term_mkAuxName_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__24;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__56;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__39;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__31;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__8;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__11;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__5;
lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__3;
lean_object* l_Lean_Meta_zetaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___closed__0;
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
static lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__3;
lean_object* l_Lean_Elab_Tactic_withoutRecover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_Elab_Term_PostponeBehavior_ofBool(x_2);
x_14 = 0;
x_15 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_11);
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
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_runTermElab_go___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_Elab_Tactic_runTermElab_go___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Elab_Tactic_runTermElab_go(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_runTermElab_go___redArg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = l_Lean_Elab_Term_withoutErrToSorry___at_____private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery_spec__0___redArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_15 = l_Lean_Elab_Tactic_runTermElab_go___redArg(x_2, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_box(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed), 11, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_box(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed), 12, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_14);
x_16 = 1;
x_17 = l_Lean_Elab_Term_withoutTacticIncrementality___at___Lean_Elab_Tactic_evalTactic_eval_spec__7___redArg(x_16, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_runTermElab___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_Elab_Tactic_runTermElab___redArg___lam__0(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Elab_Tactic_runTermElab___redArg___lam__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_Elab_Tactic_runTermElab___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Elab_Tactic_runTermElab(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_10, 5);
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_box(x_15);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_17);
x_19 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_dec(x_1);
lean_ctor_set(x_10, 5, x_19);
lean_inc(x_9);
x_20 = l_Lean_Elab_Tactic_runTermElab___redArg(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_21, x_9, x_22);
lean_dec(x_9);
return x_23;
}
else
{
lean_dec(x_9);
return x_20;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
x_26 = lean_ctor_get(x_10, 2);
x_27 = lean_ctor_get(x_10, 3);
x_28 = lean_ctor_get(x_10, 4);
x_29 = lean_ctor_get(x_10, 5);
x_30 = lean_ctor_get(x_10, 6);
x_31 = lean_ctor_get(x_10, 7);
x_32 = lean_ctor_get(x_10, 8);
x_33 = lean_ctor_get(x_10, 9);
x_34 = lean_ctor_get(x_10, 10);
x_35 = lean_ctor_get_uint8(x_10, sizeof(void*)*13);
x_36 = lean_ctor_get(x_10, 11);
x_37 = lean_ctor_get_uint8(x_10, sizeof(void*)*13 + 1);
x_38 = lean_ctor_get(x_10, 12);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_box(x_39);
lean_inc(x_1);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_2);
lean_closure_set(x_42, 2, x_40);
lean_closure_set(x_42, 3, x_41);
x_43 = l_Lean_replaceRef(x_1, x_29);
lean_dec(x_29);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_25);
lean_ctor_set(x_44, 2, x_26);
lean_ctor_set(x_44, 3, x_27);
lean_ctor_set(x_44, 4, x_28);
lean_ctor_set(x_44, 5, x_43);
lean_ctor_set(x_44, 6, x_30);
lean_ctor_set(x_44, 7, x_31);
lean_ctor_set(x_44, 8, x_32);
lean_ctor_set(x_44, 9, x_33);
lean_ctor_set(x_44, 10, x_34);
lean_ctor_set(x_44, 11, x_36);
lean_ctor_set(x_44, 12, x_38);
lean_ctor_set_uint8(x_44, sizeof(void*)*13, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*13 + 1, x_37);
lean_inc(x_9);
x_45 = l_Lean_Elab_Tactic_runTermElab___redArg(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_46, x_9, x_47);
lean_dec(x_9);
return x_48;
}
else
{
lean_dec(x_9);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_2);
x_13 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_14);
x_17 = lean_infer_type(x_14, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_32 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 8);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_8, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_8, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_8, 6);
lean_inc(x_39);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; uint8_t x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_42 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
x_43 = 1;
lean_ctor_set_uint8(x_32, 7, x_43);
x_44 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_32);
x_45 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_35);
lean_ctor_set(x_45, 3, x_36);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_38);
lean_ctor_set(x_45, 6, x_39);
lean_ctor_set_uint64(x_45, sizeof(void*)*7, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*7 + 8, x_33);
lean_ctor_set_uint8(x_45, sizeof(void*)*7 + 9, x_41);
lean_ctor_set_uint8(x_45, sizeof(void*)*7 + 10, x_42);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_16);
lean_inc(x_18);
x_46 = l_Lean_Meta_isExprDefEq(x_18, x_16, x_45, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_21 = x_49;
x_22 = x_48;
goto block_31;
}
else
{
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec_ref(x_46);
x_52 = lean_unbox(x_50);
lean_dec(x_50);
x_21 = x_52;
x_22 = x_51;
goto block_31;
}
else
{
uint8_t x_53; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; 
x_57 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_58 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
x_59 = lean_ctor_get_uint8(x_32, 0);
x_60 = lean_ctor_get_uint8(x_32, 1);
x_61 = lean_ctor_get_uint8(x_32, 2);
x_62 = lean_ctor_get_uint8(x_32, 3);
x_63 = lean_ctor_get_uint8(x_32, 4);
x_64 = lean_ctor_get_uint8(x_32, 5);
x_65 = lean_ctor_get_uint8(x_32, 6);
x_66 = lean_ctor_get_uint8(x_32, 8);
x_67 = lean_ctor_get_uint8(x_32, 9);
x_68 = lean_ctor_get_uint8(x_32, 10);
x_69 = lean_ctor_get_uint8(x_32, 11);
x_70 = lean_ctor_get_uint8(x_32, 12);
x_71 = lean_ctor_get_uint8(x_32, 13);
x_72 = lean_ctor_get_uint8(x_32, 14);
x_73 = lean_ctor_get_uint8(x_32, 15);
x_74 = lean_ctor_get_uint8(x_32, 16);
x_75 = lean_ctor_get_uint8(x_32, 17);
x_76 = lean_ctor_get_uint8(x_32, 18);
lean_dec(x_32);
x_77 = 1;
x_78 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_78, 0, x_59);
lean_ctor_set_uint8(x_78, 1, x_60);
lean_ctor_set_uint8(x_78, 2, x_61);
lean_ctor_set_uint8(x_78, 3, x_62);
lean_ctor_set_uint8(x_78, 4, x_63);
lean_ctor_set_uint8(x_78, 5, x_64);
lean_ctor_set_uint8(x_78, 6, x_65);
lean_ctor_set_uint8(x_78, 7, x_77);
lean_ctor_set_uint8(x_78, 8, x_66);
lean_ctor_set_uint8(x_78, 9, x_67);
lean_ctor_set_uint8(x_78, 10, x_68);
lean_ctor_set_uint8(x_78, 11, x_69);
lean_ctor_set_uint8(x_78, 12, x_70);
lean_ctor_set_uint8(x_78, 13, x_71);
lean_ctor_set_uint8(x_78, 14, x_72);
lean_ctor_set_uint8(x_78, 15, x_73);
lean_ctor_set_uint8(x_78, 16, x_74);
lean_ctor_set_uint8(x_78, 17, x_75);
lean_ctor_set_uint8(x_78, 18, x_76);
x_79 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_78);
x_80 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_34);
lean_ctor_set(x_80, 2, x_35);
lean_ctor_set(x_80, 3, x_36);
lean_ctor_set(x_80, 4, x_37);
lean_ctor_set(x_80, 5, x_38);
lean_ctor_set(x_80, 6, x_39);
lean_ctor_set_uint64(x_80, sizeof(void*)*7, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 8, x_33);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 9, x_57);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 10, x_58);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_16);
lean_inc(x_18);
x_81 = l_Lean_Meta_isExprDefEq(x_18, x_16, x_80, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_unbox(x_82);
lean_dec(x_82);
x_21 = x_84;
x_22 = x_83;
goto block_31;
}
else
{
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_dec_ref(x_81);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_21 = x_87;
x_22 = x_86;
goto block_31;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_90 = x_81;
} else {
 lean_dec_ref(x_81);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
block_31:
{
if (x_21 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Term_throwTypeMismatchError___redArg(x_23, x_16, x_18, x_14, x_24, x_8, x_9, x_10, x_11, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_is_scalar(x_20)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_20;
}
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_17;
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Elab_Tactic_elabTermEnsuringType(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_abortTacticExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec_ref(x_12);
x_22 = l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg(x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_filterOldMVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_uget(x_3, x_4);
lean_inc(x_13);
lean_inc_ref(x_1);
x_14 = l_Lean_MetavarContext_getDecl(x_1, x_13);
x_15 = lean_ctor_get(x_14, 6);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_nat_dec_le(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_13);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_17; 
x_17 = lean_array_push(x_6, x_13);
x_7 = x_17;
goto block_11;
}
}
else
{
lean_dec_ref(x_1);
return x_6;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_6 = x_7;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_1);
x_10 = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
x_11 = lean_nat_dec_lt(x_8, x_9);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_9);
if (x_12 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_13);
lean_dec(x_7);
x_14 = 0;
x_15 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_filterOldMVars_spec__0(x_13, x_2, x_1, x_14, x_15, x_10);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_1);
x_21 = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
x_22 = lean_nat_dec_lt(x_19, x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_20, x_20);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_26);
lean_dec(x_17);
x_27 = 0;
x_28 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_29 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_filterOldMVars_spec__0(x_26, x_2, x_1, x_27, x_28, x_21);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_filterOldMVars___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_filterOldMVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_filterOldMVars_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_filterOldMVars___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_filterOldMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attempting to close the goal using", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nthis is often due occurs-check failure", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_MVarId_getType(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_1);
x_18 = l_Lean_MVarId_getTag(x_1, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_21 = lean_apply_11(x_2, x_16, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
if (x_4 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_23;
goto block_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_22);
x_51 = l_Lean_Meta_getMVars(x_22, x_10, x_11, x_12, x_13, x_23);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = l_Lean_Elab_Tactic_filterOldMVars___redArg(x_52, x_5, x_11, x_53);
lean_dec(x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_57 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_55, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_56);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_58;
goto block_50;
}
else
{
lean_dec(x_22);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_57;
}
}
block_50:
{
lean_object* x_29; 
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_22);
lean_inc(x_1);
x_29 = lean_checked_assign(x_1, x_22, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1;
x_34 = l_Lean_indentExpr(x_22);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_Meta_throwTacticEx___redArg(x_3, x_1, x_38, x_24, x_25, x_26, x_27, x_32);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_29);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_29, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_29, 0, x_42);
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_box(0);
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
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
return x_29;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_29, 0);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_29);
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
uint8_t x_59; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_21);
if (x_59 == 0)
{
return x_21;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_21, 0);
x_61 = lean_ctor_get(x_21, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_21);
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
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_18);
if (x_63 == 0)
{
return x_18;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_18, 0);
x_65 = lean_ctor_get(x_18, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_18);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_15);
if (x_67 == 0)
{
return x_15;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_15, 0);
x_69 = lean_ctor_get(x_15, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_15);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_st_ref_get(x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Elab_Tactic_popMainGoal___redArg(x_5, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = lean_box(x_3);
lean_inc(x_18);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed), 14, 5);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_21);
lean_closure_set(x_22, 4, x_20);
lean_inc(x_5);
lean_inc(x_18);
x_23 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_withMainContext_spec__0___redArg(x_18, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_18);
lean_dec(x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_33; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_33 = l_Lean_Exception_isInterrupt(x_24);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Exception_isRuntime(x_24);
x_26 = x_34;
goto block_32;
}
else
{
x_26 = x_33;
goto block_32;
}
block_32:
{
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec_ref(x_23);
x_27 = l_Lean_Elab_Tactic_pushGoal___redArg(x_18, x_5, x_25);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_5);
return x_23;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
x_16 = l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Elab_Tactic_closeMainGoalUsing(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = 0;
x_15 = l_Lean_Elab_Tactic_elabTermEnsuringType(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalExact___closed__4;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___lam__0___boxed), 12, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Tactic_evalExact___closed__5;
x_18 = l_Lean_Elab_Tactic_closeMainGoalUsing(x_17, x_16, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalExact___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalExact", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__4;
x_4 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = lean_unsigned_to_nat(71u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(78u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(26u);
x_4 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = lean_unsigned_to_nat(71u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(39u);
x_2 = lean_unsigned_to_nat(71u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(39u);
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(30u);
x_4 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_4 = l_Lean_MetavarContext_getDecl(x_1, x_2);
x_5 = lean_ctor_get(x_4, 6);
lean_inc(x_5);
lean_dec_ref(x_4);
lean_inc(x_3);
x_6 = l_Lean_MetavarContext_getDecl(x_1, x_3);
x_7 = lean_ctor_get(x_6, 6);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_5);
x_10 = l_Lean_Name_quickLt(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_18; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_7, 0, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_18 = lean_nat_dec_le(x_5, x_14);
if (x_18 == 0)
{
lean_inc(x_14);
x_15 = x_14;
goto block_17;
}
else
{
x_15 = x_5;
goto block_17;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_qsort_sort___redArg(x_7, x_1, x_8, x_9);
lean_dec(x_9);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
return x_11;
}
block_17:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_15, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
lean_inc(x_15);
x_8 = x_15;
x_9 = x_15;
goto block_12;
}
else
{
x_8 = x_15;
x_9 = x_14;
goto block_12;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_19 = lean_apply_2(x_2, lean_box(0), x_1);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__1), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_to_list(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_array_mk(x_3);
x_8 = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___redArg(x_1, x_2, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_sortMVarIdsByIndex___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_4 = l_Lean_MetavarContext_getDecl(x_1, x_2);
x_5 = lean_ctor_get(x_4, 6);
lean_inc(x_5);
lean_dec_ref(x_4);
lean_inc(x_3);
x_6 = l_Lean_MetavarContext_getDecl(x_1, x_3);
x_7 = lean_ctor_get(x_6, 6);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_5);
x_10 = l_Lean_Name_quickLt(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_6, 0, x_1);
lean_inc(x_3);
x_7 = l_Array_qpartition___redArg(x_2, x_6, x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_nat_dec_le(x_4, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc_ref(x_1);
x_11 = l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg(x_1, x_9, x_3, x_8);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg(x_1, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_8);
lean_dec(x_5);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_22; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_22 = lean_nat_dec_le(x_15, x_18);
if (x_22 == 0)
{
lean_inc(x_18);
x_19 = x_18;
goto block_21;
}
else
{
x_19 = x_15;
goto block_21;
}
block_21:
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_19, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_inc(x_19);
x_9 = x_19;
x_10 = x_19;
goto block_13;
}
else
{
x_9 = x_19;
x_10 = x_18;
goto block_13;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_14);
lean_dec_ref(x_8);
lean_dec(x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg(x_8, x_1, x_9, x_10);
lean_dec(x_10);
if (lean_is_scalar(x_7)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_7;
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(x_1, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_mk(x_1);
x_12 = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(x_11, x_7, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_array_to_list(x_14);
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
x_18 = lean_array_to_list(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_11);
x_12 = l_Lean_MVarId_getKind(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_20 = lean_unbox(x_13);
lean_dec(x_13);
x_21 = l_Lean_MetavarKind_isNatural(x_20);
if (x_21 == 0)
{
lean_dec(x_11);
x_15 = x_4;
goto block_19;
}
else
{
lean_object* x_22; 
x_22 = lean_array_push(x_4, x_11);
x_15 = x_22;
goto block_19;
}
block_19:
{
size_t x_16; size_t x_17; 
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
x_9 = x_14;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec_ref(x_4);
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
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_2, x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_array_uget(x_1, x_2);
lean_inc(x_19);
x_23 = l_Lean_Elab_Term_isLetRecAuxMVar(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec_ref(x_23);
x_20 = x_26;
goto block_22;
}
else
{
lean_object* x_27; 
lean_dec(x_19);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec_ref(x_23);
x_12 = x_4;
x_13 = x_27;
goto block_17;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_array_push(x_4, x_19);
x_12 = x_21;
x_13 = x_20;
goto block_17;
}
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_11);
return x_28;
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_st_ref_get(x_10, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_17 = lean_apply_9(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc(x_18);
x_58 = l_Lean_Meta_getMVarsNoDelayed(x_18, x_9, x_10, x_11, x_12, x_19);
x_59 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_59);
lean_dec(x_15);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec_ref(x_58);
x_62 = lean_ctor_get(x_59, 2);
lean_inc(x_62);
lean_dec_ref(x_59);
x_63 = lean_unsigned_to_nat(0u);
x_85 = lean_array_get_size(x_60);
x_86 = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
x_87 = lean_nat_dec_lt(x_63, x_85);
if (x_87 == 0)
{
lean_dec(x_85);
lean_dec(x_60);
x_64 = x_86;
x_65 = x_61;
goto block_84;
}
else
{
uint8_t x_88; 
x_88 = lean_nat_dec_le(x_85, x_85);
if (x_88 == 0)
{
lean_dec(x_85);
lean_dec(x_60);
x_64 = x_86;
x_65 = x_61;
goto block_84;
}
else
{
size_t x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = 0;
x_90 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_91 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4___redArg(x_60, x_89, x_90, x_86, x_7, x_8, x_9, x_10, x_11, x_12, x_61);
lean_dec(x_60);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_64 = x_92;
x_65 = x_93;
goto block_84;
}
}
block_47:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_array_to_list(x_20);
x_31 = l_Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(x_30, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_35 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_2, x_3, x_33, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_34);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_31, 1, x_33);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_35, 0, x_31);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_31, 1, x_33);
lean_ctor_set(x_31, 0, x_18);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
lean_inc(x_40);
x_42 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_2, x_3, x_40, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_41);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_40);
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
block_57:
{
lean_object* x_51; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_51 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_50);
lean_dec_ref(x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_20 = x_48;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
x_27 = x_11;
x_28 = x_12;
x_29 = x_52;
goto block_47;
}
else
{
uint8_t x_53; 
lean_dec_ref(x_48);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
block_84:
{
lean_object* x_66; 
x_66 = l_Lean_Elab_Tactic_filterOldMVars___redArg(x_64, x_62, x_10, x_65);
lean_dec(x_62);
lean_dec_ref(x_64);
if (x_4 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = lean_array_get_size(x_67);
x_70 = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
x_71 = lean_nat_dec_lt(x_63, x_69);
if (x_71 == 0)
{
lean_dec(x_69);
x_48 = x_67;
x_49 = x_70;
x_50 = x_68;
goto block_57;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_69, x_69);
if (x_72 == 0)
{
lean_dec(x_69);
x_48 = x_67;
x_49 = x_70;
x_50 = x_68;
goto block_57;
}
else
{
size_t x_73; size_t x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_75 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3___redArg(x_67, x_73, x_74, x_70, x_9, x_10, x_11, x_12, x_68);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_48 = x_67;
x_49 = x_76;
x_50 = x_77;
goto block_57;
}
else
{
uint8_t x_78; 
lean_dec(x_67);
lean_dec(x_18);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_66, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_dec_ref(x_66);
x_20 = x_82;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
x_27 = x_11;
x_28 = x_12;
x_29 = x_83;
goto block_47;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_17);
if (x_94 == 0)
{
return x_17;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_17, 0);
x_96 = lean_ctor_get(x_17, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_17);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_qsort_sort___at___Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at___Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_sortMVarIdsByIndex___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__3(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4___redArg(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_withCollectingNewGoalsFrom_go_spec__4(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_4 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_7, sizeof(void*)*7);
x_18 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 1);
x_19 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 2);
x_20 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_7, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 5);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 3);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 4);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 5);
x_27 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 6);
x_28 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 7);
x_29 = lean_ctor_get(x_7, 6);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_31 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_32 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 x_33 = x_7;
} else {
 lean_dec_ref(x_7);
 x_33 = lean_box(0);
}
if (x_31 == 0)
{
x_34 = x_4;
goto block_109;
}
else
{
x_34 = x_31;
goto block_109;
}
block_109:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_9, 0);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint64_t x_39; lean_object* x_40; 
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(0, 7, 11);
} else {
 x_38 = x_33;
}
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_16);
lean_ctor_set(x_38, 2, x_20);
lean_ctor_set(x_38, 3, x_21);
lean_ctor_set(x_38, 4, x_22);
lean_ctor_set(x_38, 5, x_23);
lean_ctor_set(x_38, 6, x_29);
lean_ctor_set_uint8(x_38, sizeof(void*)*7, x_17);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 1, x_18);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 2, x_19);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 3, x_24);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 4, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 5, x_26);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 6, x_27);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 7, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 8, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 9, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 10, x_32);
lean_ctor_set_uint8(x_36, 7, x_4);
x_39 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_36);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_39);
x_40 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_38, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
return x_40;
}
}
else
{
uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; 
x_45 = lean_ctor_get_uint8(x_36, 0);
x_46 = lean_ctor_get_uint8(x_36, 1);
x_47 = lean_ctor_get_uint8(x_36, 2);
x_48 = lean_ctor_get_uint8(x_36, 3);
x_49 = lean_ctor_get_uint8(x_36, 4);
x_50 = lean_ctor_get_uint8(x_36, 5);
x_51 = lean_ctor_get_uint8(x_36, 6);
x_52 = lean_ctor_get_uint8(x_36, 8);
x_53 = lean_ctor_get_uint8(x_36, 9);
x_54 = lean_ctor_get_uint8(x_36, 10);
x_55 = lean_ctor_get_uint8(x_36, 11);
x_56 = lean_ctor_get_uint8(x_36, 12);
x_57 = lean_ctor_get_uint8(x_36, 13);
x_58 = lean_ctor_get_uint8(x_36, 14);
x_59 = lean_ctor_get_uint8(x_36, 15);
x_60 = lean_ctor_get_uint8(x_36, 16);
x_61 = lean_ctor_get_uint8(x_36, 17);
x_62 = lean_ctor_get_uint8(x_36, 18);
lean_dec(x_36);
if (lean_is_scalar(x_33)) {
 x_63 = lean_alloc_ctor(0, 7, 11);
} else {
 x_63 = x_33;
}
lean_ctor_set(x_63, 0, x_15);
lean_ctor_set(x_63, 1, x_16);
lean_ctor_set(x_63, 2, x_20);
lean_ctor_set(x_63, 3, x_21);
lean_ctor_set(x_63, 4, x_22);
lean_ctor_set(x_63, 5, x_23);
lean_ctor_set(x_63, 6, x_29);
lean_ctor_set_uint8(x_63, sizeof(void*)*7, x_17);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 1, x_18);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 2, x_19);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 3, x_24);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 4, x_25);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 5, x_26);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 6, x_27);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 7, x_28);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 8, x_30);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 9, x_34);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 10, x_32);
x_64 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_64, 0, x_45);
lean_ctor_set_uint8(x_64, 1, x_46);
lean_ctor_set_uint8(x_64, 2, x_47);
lean_ctor_set_uint8(x_64, 3, x_48);
lean_ctor_set_uint8(x_64, 4, x_49);
lean_ctor_set_uint8(x_64, 5, x_50);
lean_ctor_set_uint8(x_64, 6, x_51);
lean_ctor_set_uint8(x_64, 7, x_4);
lean_ctor_set_uint8(x_64, 8, x_52);
lean_ctor_set_uint8(x_64, 9, x_53);
lean_ctor_set_uint8(x_64, 10, x_54);
lean_ctor_set_uint8(x_64, 11, x_55);
lean_ctor_set_uint8(x_64, 12, x_56);
lean_ctor_set_uint8(x_64, 13, x_57);
lean_ctor_set_uint8(x_64, 14, x_58);
lean_ctor_set_uint8(x_64, 15, x_59);
lean_ctor_set_uint8(x_64, 16, x_60);
lean_ctor_set_uint8(x_64, 17, x_61);
lean_ctor_set_uint8(x_64, 18, x_62);
x_65 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_64);
lean_ctor_set(x_9, 0, x_64);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_65);
x_66 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_63, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
return x_66;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint64_t x_102; lean_object* x_103; lean_object* x_104; 
x_71 = lean_ctor_get(x_9, 0);
x_72 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_73 = lean_ctor_get(x_9, 1);
x_74 = lean_ctor_get(x_9, 2);
x_75 = lean_ctor_get(x_9, 3);
x_76 = lean_ctor_get(x_9, 4);
x_77 = lean_ctor_get(x_9, 5);
x_78 = lean_ctor_get(x_9, 6);
x_79 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_80 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_71);
lean_dec(x_9);
x_81 = lean_ctor_get_uint8(x_71, 0);
x_82 = lean_ctor_get_uint8(x_71, 1);
x_83 = lean_ctor_get_uint8(x_71, 2);
x_84 = lean_ctor_get_uint8(x_71, 3);
x_85 = lean_ctor_get_uint8(x_71, 4);
x_86 = lean_ctor_get_uint8(x_71, 5);
x_87 = lean_ctor_get_uint8(x_71, 6);
x_88 = lean_ctor_get_uint8(x_71, 8);
x_89 = lean_ctor_get_uint8(x_71, 9);
x_90 = lean_ctor_get_uint8(x_71, 10);
x_91 = lean_ctor_get_uint8(x_71, 11);
x_92 = lean_ctor_get_uint8(x_71, 12);
x_93 = lean_ctor_get_uint8(x_71, 13);
x_94 = lean_ctor_get_uint8(x_71, 14);
x_95 = lean_ctor_get_uint8(x_71, 15);
x_96 = lean_ctor_get_uint8(x_71, 16);
x_97 = lean_ctor_get_uint8(x_71, 17);
x_98 = lean_ctor_get_uint8(x_71, 18);
if (lean_is_exclusive(x_71)) {
 x_99 = x_71;
} else {
 lean_dec_ref(x_71);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_100 = lean_alloc_ctor(0, 7, 11);
} else {
 x_100 = x_33;
}
lean_ctor_set(x_100, 0, x_15);
lean_ctor_set(x_100, 1, x_16);
lean_ctor_set(x_100, 2, x_20);
lean_ctor_set(x_100, 3, x_21);
lean_ctor_set(x_100, 4, x_22);
lean_ctor_set(x_100, 5, x_23);
lean_ctor_set(x_100, 6, x_29);
lean_ctor_set_uint8(x_100, sizeof(void*)*7, x_17);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 1, x_18);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 2, x_19);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 3, x_24);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 4, x_25);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 5, x_26);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 6, x_27);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 7, x_28);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 8, x_30);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 9, x_34);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 10, x_32);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 0, 19);
} else {
 x_101 = x_99;
}
lean_ctor_set_uint8(x_101, 0, x_81);
lean_ctor_set_uint8(x_101, 1, x_82);
lean_ctor_set_uint8(x_101, 2, x_83);
lean_ctor_set_uint8(x_101, 3, x_84);
lean_ctor_set_uint8(x_101, 4, x_85);
lean_ctor_set_uint8(x_101, 5, x_86);
lean_ctor_set_uint8(x_101, 6, x_87);
lean_ctor_set_uint8(x_101, 7, x_4);
lean_ctor_set_uint8(x_101, 8, x_88);
lean_ctor_set_uint8(x_101, 9, x_89);
lean_ctor_set_uint8(x_101, 10, x_90);
lean_ctor_set_uint8(x_101, 11, x_91);
lean_ctor_set_uint8(x_101, 12, x_92);
lean_ctor_set_uint8(x_101, 13, x_93);
lean_ctor_set_uint8(x_101, 14, x_94);
lean_ctor_set_uint8(x_101, 15, x_95);
lean_ctor_set_uint8(x_101, 16, x_96);
lean_ctor_set_uint8(x_101, 17, x_97);
lean_ctor_set_uint8(x_101, 18, x_98);
x_102 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_101);
x_103 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_73);
lean_ctor_set(x_103, 2, x_74);
lean_ctor_set(x_103, 3, x_75);
lean_ctor_set(x_103, 4, x_76);
lean_ctor_set(x_103, 5, x_77);
lean_ctor_set(x_103, 6, x_78);
lean_ctor_set_uint64(x_103, sizeof(void*)*7, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 8, x_72);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 9, x_79);
lean_ctor_set_uint8(x_103, sizeof(void*)*7 + 10, x_80);
x_104 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_100, x_8, x_103, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
return x_104;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Tactic_getMainTag___redArg(x_7, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_15 = x_23;
x_16 = x_24;
goto block_21;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
x_15 = x_29;
x_16 = x_14;
goto block_21;
}
block_21:
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermEnsuringType___boxed), 12, 3);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(x_19, x_15, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_16);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
x_16 = l_Lean_Elab_Tactic_elabTermWithHoles(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_7, 7);
x_13 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_12, x_1, x_2);
lean_ctor_set(x_7, 7, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 2);
x_24 = lean_ctor_get(x_7, 3);
x_25 = lean_ctor_get(x_7, 4);
x_26 = lean_ctor_get(x_7, 5);
x_27 = lean_ctor_get(x_7, 6);
x_28 = lean_ctor_get(x_7, 7);
x_29 = lean_ctor_get(x_7, 8);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_30 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_28, x_1, x_2);
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set(x_31, 3, x_24);
lean_ctor_set(x_31, 4, x_25);
lean_ctor_set(x_31, 5, x_26);
lean_ctor_set(x_31, 6, x_27);
lean_ctor_set(x_31, 7, x_30);
lean_ctor_set(x_31, 8, x_29);
lean_ctor_set(x_6, 0, x_31);
x_32 = lean_st_ref_set(x_3, x_6, x_8);
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
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_37 = lean_ctor_get(x_6, 1);
x_38 = lean_ctor_get(x_6, 2);
x_39 = lean_ctor_get(x_6, 3);
x_40 = lean_ctor_get(x_6, 4);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_7, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_7, 5);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_7, 6);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_7, 7);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_7, 8);
lean_inc_ref(x_49);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_50 = x_7;
} else {
 lean_dec_ref(x_7);
 x_50 = lean_box(0);
}
x_51 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_48, x_1, x_2);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 9, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set(x_52, 3, x_44);
lean_ctor_set(x_52, 4, x_45);
lean_ctor_set(x_52, 5, x_46);
lean_ctor_set(x_52, 6, x_47);
lean_ctor_set(x_52, 7, x_51);
lean_ctor_set(x_52, 8, x_49);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_37);
lean_ctor_set(x_53, 2, x_38);
lean_ctor_set(x_53, 3, x_39);
lean_ctor_set(x_53, 4, x_40);
x_54 = lean_st_ref_set(x_3, x_53, x_8);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(x_1, x_2, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'refine' tactic failed, value", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_refineCore___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ndepends on the main goal metavariable '", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_refineCore___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_refineCore___lam__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_getMainTarget(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_box(0);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_5);
x_18 = l_Lean_Elab_Tactic_elabTermWithHoles(x_1, x_16, x_2, x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_23 = x_19;
} else {
 lean_dec_ref(x_19);
 x_23 = lean_box(0);
}
x_24 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_5, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_43; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_21, x_9, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
lean_inc(x_25);
x_31 = l_Lean_Expr_mvar___override(x_25);
x_43 = lean_expr_eqv(x_28, x_31);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_inc(x_25);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lam__0___boxed), 2, 1);
lean_closure_set(x_44, 0, x_25);
lean_inc(x_28);
x_45 = l_Lean_FindMVar_main(x_44, x_28, x_17);
if (lean_obj_tag(x_45) == 0)
{
if (x_43 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_23);
x_46 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(x_25, x_28, x_9, x_29);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_22, x_5, x_8, x_9, x_10, x_11, x_47);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
return x_48;
}
else
{
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_5);
goto block_42;
}
}
else
{
lean_dec(x_45);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_5);
goto block_42;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_22);
x_50 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_49, x_5, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
return x_50;
}
block_42:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = l_Lean_Elab_Tactic_refineCore___lam__1___closed__1;
x_33 = l_Lean_indentExpr(x_28);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(7, 2, 0);
} else {
 x_34 = x_30;
 lean_ctor_set_tag(x_34, 7);
}
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_Tactic_refineCore___lam__1___closed__3;
if (lean_is_scalar(x_23)) {
 x_36 = lean_alloc_ctor(7, 2, 0);
} else {
 x_36 = x_23;
 lean_ctor_set_tag(x_36, 7);
}
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_MessageData_ofExpr(x_31);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_Tactic_refineCore___lam__1___closed__5;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_40, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_41;
}
}
else
{
uint8_t x_51; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
return x_24;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_24, 0);
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_24);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
x_55 = !lean_is_exclusive(x_18);
if (x_55 == 0)
{
return x_18;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = lean_ctor_get(x_18, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_18);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_13);
if (x_59 == 0)
{
return x_13;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_13, 0);
x_61 = lean_ctor_get(x_13, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_13);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lam__1___boxed), 12, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_13);
x_15 = l_Lean_Elab_Tactic_withMainContext___redArg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assign___at___Lean_Elab_Tactic_refineCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Tactic_refineCore___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Elab_Tactic_refineCore___lam__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Elab_Tactic_refineCore(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refine", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalRefine___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRefine___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalRefine___closed__1;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Elab_Tactic_evalRefine___closed__2;
x_17 = 0;
x_18 = l_Lean_Elab_Tactic_refineCore(x_15, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalRefine", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalRefine___closed__1;
x_4 = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(27u);
x_2 = lean_unsigned_to_nat(189u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = lean_unsigned_to_nat(192u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(27u);
x_4 = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(189u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(41u);
x_2 = lean_unsigned_to_nat(189u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(41u);
x_2 = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(31u);
x_4 = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1;
x_3 = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refine'", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalRefine_x27___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRefine_x27___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalRefine_x27___closed__1;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Elab_Tactic_evalRefine_x27___closed__2;
x_17 = l_Lean_Elab_Tactic_refineCore(x_15, x_16, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalRefine'", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalRefine_x27___closed__1;
x_4 = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine_x27), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_unsigned_to_nat(194u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = lean_unsigned_to_nat(197u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(28u);
x_4 = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_unsigned_to_nat(194u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(43u);
x_2 = lean_unsigned_to_nat(194u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(43u);
x_2 = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(32u);
x_4 = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1;
x_3 = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'specialize' requires a term of the form `h x_1 .. x_n` where `h` appears in the local context", 94, 94);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_1 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_2, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Name_mkStr1(x_3);
x_19 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_6);
x_20 = l_Lean_Elab_Tactic_elabTermWithHoles(x_16, x_17, x_18, x_4, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Expr_getAppFn(x_23);
x_26 = l_Lean_Expr_isFVar(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_6);
x_27 = l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1;
x_28 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_27, x_9, x_10, x_11, x_12, x_22);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec_ref(x_25);
lean_inc_ref(x_9);
lean_inc(x_29);
x_30 = l_Lean_FVarId_getDecl___redArg(x_29, x_9, x_11, x_12, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_6, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_23);
x_36 = lean_infer_type(x_23, x_9, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_81; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_81 = lean_ctor_get(x_31, 2);
lean_inc(x_81);
lean_dec(x_31);
x_39 = x_81;
goto block_80;
block_80:
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_Expr_headBeta(x_37);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_41 = l_Lean_MVarId_assert(x_34, x_39, x_40, x_23, x_9, x_10, x_11, x_12, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_44 = l_Lean_Meta_intro1Core(x_42, x_26, x_9, x_10, x_11, x_12, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_50 = l_Lean_MVarId_tryClear(x_48, x_29, x_9, x_10, x_11, x_12, x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_box(0);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 1, x_53);
lean_ctor_set(x_45, 0, x_51);
x_54 = l_List_appendTR___redArg(x_24, x_45);
x_55 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_54, x_6, x_9, x_10, x_11, x_12, x_52);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
return x_55;
}
else
{
uint8_t x_56; 
lean_free_object(x_45);
lean_dec(x_24);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_50);
if (x_56 == 0)
{
return x_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_50, 0);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_dec(x_45);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_61 = l_Lean_MVarId_tryClear(x_60, x_29, x_9, x_10, x_11, x_12, x_46);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_List_appendTR___redArg(x_24, x_65);
x_67 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_66, x_6, x_9, x_10, x_11, x_12, x_63);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_24);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_70 = x_61;
} else {
 lean_dec_ref(x_61);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
x_72 = !lean_is_exclusive(x_44);
if (x_72 == 0)
{
return x_44;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_44, 0);
x_74 = lean_ctor_get(x_44, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_44);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
x_76 = !lean_is_exclusive(x_41);
if (x_76 == 0)
{
return x_41;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_41, 0);
x_78 = lean_ctor_get(x_41, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_41);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
x_82 = !lean_is_exclusive(x_36);
if (x_82 == 0)
{
return x_36;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_36, 0);
x_84 = lean_ctor_get(x_36, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_36);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
x_86 = !lean_is_exclusive(x_33);
if (x_86 == 0)
{
return x_33;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_33, 0);
x_88 = lean_ctor_get(x_33, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_33);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
x_90 = !lean_is_exclusive(x_30);
if (x_90 == 0)
{
return x_30;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_30, 0);
x_92 = lean_ctor_get(x_30, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_30);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
x_94 = !lean_is_exclusive(x_20);
if (x_94 == 0)
{
return x_20;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_20, 0);
x_96 = lean_ctor_get(x_20, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_20);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("specialize", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSpecialize___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = l_Lean_Elab_Tactic_evalSpecialize___closed__0;
x_12 = l_Lean_Elab_Tactic_evalSpecialize___closed__1;
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
x_14 = 1;
x_15 = lean_box(x_13);
x_16 = lean_box(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed), 13, 4);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_11);
lean_closure_set(x_17, 3, x_16);
x_18 = l_Lean_Elab_Tactic_withMainContext___redArg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
x_15 = lean_unbox(x_4);
x_16 = l_Lean_Elab_Tactic_evalSpecialize___lam__0(x_14, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSpecialize", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalSpecialize___closed__1;
x_4 = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(199u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(212u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1;
x_2 = lean_unsigned_to_nat(31u);
x_3 = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(199u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(49u);
x_2 = lean_unsigned_to_nat(199u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(49u);
x_2 = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(35u);
x_4 = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1;
x_3 = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTermForApply___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_24; 
x_24 = l_Lean_Syntax_isIdent(x_1);
if (x_24 == 0)
{
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
goto block_23;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Elab_Tactic_elabTermForApply___closed__0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_26 = l_Lean_Elab_Term_resolveId_x3f(x_1, x_25, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_28;
goto block_23;
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 0);
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
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
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
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
return x_26;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_26);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_23:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Tactic_elabTerm(x_1, x_21, x_2, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_Elab_Tactic_elabTermForApply(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected term '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'; expected single reference to variable", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_11 = l_Lean_Elab_Tactic_withoutRecover___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec_ref(x_11);
x_20 = l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1;
x_21 = l_Lean_MessageData_ofExpr(x_12);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_24, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_8, 5);
x_13 = 0;
x_14 = lean_box(x_13);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId___lam__0), 10, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_8, 5, x_17);
x_18 = l_Lean_Elab_Tactic_withMainContext___redArg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
x_21 = lean_ctor_get(x_8, 2);
x_22 = lean_ctor_get(x_8, 3);
x_23 = lean_ctor_get(x_8, 4);
x_24 = lean_ctor_get(x_8, 5);
x_25 = lean_ctor_get(x_8, 6);
x_26 = lean_ctor_get(x_8, 7);
x_27 = lean_ctor_get(x_8, 8);
x_28 = lean_ctor_get(x_8, 9);
x_29 = lean_ctor_get(x_8, 10);
x_30 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_31 = lean_ctor_get(x_8, 11);
x_32 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_33 = lean_ctor_get(x_8, 12);
lean_inc(x_33);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_34 = 0;
x_35 = lean_box(x_34);
lean_inc(x_1);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_35);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId___lam__0), 10, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = l_Lean_replaceRef(x_1, x_24);
lean_dec(x_24);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_20);
lean_ctor_set(x_39, 2, x_21);
lean_ctor_set(x_39, 3, x_22);
lean_ctor_set(x_39, 4, x_23);
lean_ctor_set(x_39, 5, x_38);
lean_ctor_set(x_39, 6, x_25);
lean_ctor_set(x_39, 7, x_26);
lean_ctor_set(x_39, 8, x_27);
lean_ctor_set(x_39, 9, x_28);
lean_ctor_set(x_39, 10, x_29);
lean_ctor_set(x_39, 11, x_31);
lean_ctor_set(x_39, 12, x_33);
lean_ctor_set_uint8(x_39, sizeof(void*)*13, x_30);
lean_ctor_set_uint8(x_39, sizeof(void*)*13 + 1, x_32);
x_40 = l_Lean_Elab_Tactic_withMainContext___redArg(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_39, x_9, x_10);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_getFVarIds_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_2, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_3, x_2);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_16 = l_Lean_Elab_Tactic_getFVarId(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_3, x_2, x_19);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_20, x_2, x_17);
x_2 = x_22;
x_3 = x_23;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarIds___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_size(x_1);
x_12 = lean_box_usize(x_11);
x_13 = l_Lean_Elab_Tactic_getFVarIds___boxed__const__1;
x_14 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_getFVarIds_spec__0___boxed), 12, 3);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_1);
x_15 = l_Lean_Elab_Tactic_withMainContext___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_getFVarIds_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Array_mapMUnsafe_map___at___Lean_Elab_Tactic_getFVarIds_spec__0(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_41; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_41 = l_Lean_Elab_Tactic_elabTermForApply(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_42, x_9, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = l_Lean_Expr_isMVar(x_45);
if (x_47 == 0)
{
x_13 = x_45;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_46;
goto block_40;
}
else
{
uint8_t x_48; lean_object* x_49; 
x_48 = 0;
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_49 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_48, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_getMainTarget_spec__0___redArg(x_45, x_9, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_13 = x_52;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_53;
goto block_40;
}
else
{
lean_dec(x_45);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_49;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
return x_41;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
block_40:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_14, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
x_25 = lean_apply_7(x_3, x_23, x_13, x_17, x_18, x_19, x_20, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = 0;
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
x_29 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_28, x_15, x_16, x_17, x_18, x_19, x_20, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_26, x_14, x_17, x_18, x_19, x_20, x_30);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_14);
return x_31;
}
else
{
lean_dec(x_26);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_14);
return x_29;
}
}
else
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
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
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed), 12, 3);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_1);
x_15 = l_Lean_Elab_Tactic_withMainContext___redArg(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l_Lean_Elab_Tactic_evalApplyLikeTactic___lam__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalApply___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = 0;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, 1, x_1);
lean_ctor_set_uint8(x_11, 2, x_10);
lean_ctor_set_uint8(x_11, 3, x_1);
x_12 = l_Lean_Elab_Tactic_evalApply___lam__0___closed__1;
lean_inc_ref(x_3);
x_13 = l_Lean_MessageData_ofExpr(x_3);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MVarId_apply(x_2, x_3, x_11, x_16, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("apply", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalApply___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalApply___closed__1;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_box(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___lam__0___boxed), 8, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = l_Lean_Elab_Tactic_evalApplyLikeTactic(x_15, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lean_Elab_Tactic_evalApply___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalApply", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalApply___closed__1;
x_4 = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(43u);
x_2 = lean_unsigned_to_nat(303u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(306u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(43u);
x_4 = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(47u);
x_2 = lean_unsigned_to_nat(303u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(56u);
x_2 = lean_unsigned_to_nat(303u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(56u);
x_2 = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(47u);
x_4 = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1;
x_3 = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = 0;
x_14 = l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_15 = l_Lean_MVarId_constructor(x_11, x_14, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_18 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_16, x_2, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_20;
}
else
{
lean_dec(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_18;
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
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
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___boxed), 9, 0);
x_11 = l_Lean_Elab_Tactic_withMainContext___redArg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalConstructor___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalConstructor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("constructor", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalConstructor", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalConstructor___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(49u);
x_2 = lean_unsigned_to_nat(308u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_unsigned_to_nat(312u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(49u);
x_4 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(53u);
x_2 = lean_unsigned_to_nat(308u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(68u);
x_2 = lean_unsigned_to_nat(308u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(68u);
x_2 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(53u);
x_4 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithReducible___closed__0() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint64_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; lean_object* x_23; 
x_14 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = 2;
lean_ctor_set_uint8(x_12, 9, x_17);
x_18 = 2;
x_19 = lean_uint64_shift_right(x_14, x_18);
x_20 = lean_uint64_shift_left(x_19, x_18);
x_21 = l_Lean_Elab_Tactic_evalWithReducible___closed__0;
x_22 = lean_uint64_lor(x_20, x_21);
lean_ctor_set_uint64(x_6, sizeof(void*)*7, x_22);
x_23 = l_Lean_Elab_Tactic_evalTactic(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
return x_23;
}
}
else
{
uint64_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; lean_object* x_56; 
x_28 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_29 = lean_ctor_get_uint8(x_12, 0);
x_30 = lean_ctor_get_uint8(x_12, 1);
x_31 = lean_ctor_get_uint8(x_12, 2);
x_32 = lean_ctor_get_uint8(x_12, 3);
x_33 = lean_ctor_get_uint8(x_12, 4);
x_34 = lean_ctor_get_uint8(x_12, 5);
x_35 = lean_ctor_get_uint8(x_12, 6);
x_36 = lean_ctor_get_uint8(x_12, 7);
x_37 = lean_ctor_get_uint8(x_12, 8);
x_38 = lean_ctor_get_uint8(x_12, 10);
x_39 = lean_ctor_get_uint8(x_12, 11);
x_40 = lean_ctor_get_uint8(x_12, 12);
x_41 = lean_ctor_get_uint8(x_12, 13);
x_42 = lean_ctor_get_uint8(x_12, 14);
x_43 = lean_ctor_get_uint8(x_12, 15);
x_44 = lean_ctor_get_uint8(x_12, 16);
x_45 = lean_ctor_get_uint8(x_12, 17);
x_46 = lean_ctor_get_uint8(x_12, 18);
lean_dec(x_12);
x_47 = lean_unsigned_to_nat(1u);
x_48 = l_Lean_Syntax_getArg(x_1, x_47);
x_49 = 2;
x_50 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_50, 0, x_29);
lean_ctor_set_uint8(x_50, 1, x_30);
lean_ctor_set_uint8(x_50, 2, x_31);
lean_ctor_set_uint8(x_50, 3, x_32);
lean_ctor_set_uint8(x_50, 4, x_33);
lean_ctor_set_uint8(x_50, 5, x_34);
lean_ctor_set_uint8(x_50, 6, x_35);
lean_ctor_set_uint8(x_50, 7, x_36);
lean_ctor_set_uint8(x_50, 8, x_37);
lean_ctor_set_uint8(x_50, 9, x_49);
lean_ctor_set_uint8(x_50, 10, x_38);
lean_ctor_set_uint8(x_50, 11, x_39);
lean_ctor_set_uint8(x_50, 12, x_40);
lean_ctor_set_uint8(x_50, 13, x_41);
lean_ctor_set_uint8(x_50, 14, x_42);
lean_ctor_set_uint8(x_50, 15, x_43);
lean_ctor_set_uint8(x_50, 16, x_44);
lean_ctor_set_uint8(x_50, 17, x_45);
lean_ctor_set_uint8(x_50, 18, x_46);
x_51 = 2;
x_52 = lean_uint64_shift_right(x_28, x_51);
x_53 = lean_uint64_shift_left(x_52, x_51);
x_54 = l_Lean_Elab_Tactic_evalWithReducible___closed__0;
x_55 = lean_uint64_lor(x_53, x_54);
lean_ctor_set(x_6, 0, x_50);
lean_ctor_set_uint64(x_6, sizeof(void*)*7, x_55);
x_56 = l_Lean_Elab_Tactic_evalTactic(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
return x_56;
}
}
}
else
{
lean_object* x_61; uint64_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; lean_object* x_100; lean_object* x_101; 
x_61 = lean_ctor_get(x_6, 0);
x_62 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_63 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_64 = lean_ctor_get(x_6, 1);
x_65 = lean_ctor_get(x_6, 2);
x_66 = lean_ctor_get(x_6, 3);
x_67 = lean_ctor_get(x_6, 4);
x_68 = lean_ctor_get(x_6, 5);
x_69 = lean_ctor_get(x_6, 6);
x_70 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_71 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_61);
lean_dec(x_6);
x_72 = lean_ctor_get_uint8(x_61, 0);
x_73 = lean_ctor_get_uint8(x_61, 1);
x_74 = lean_ctor_get_uint8(x_61, 2);
x_75 = lean_ctor_get_uint8(x_61, 3);
x_76 = lean_ctor_get_uint8(x_61, 4);
x_77 = lean_ctor_get_uint8(x_61, 5);
x_78 = lean_ctor_get_uint8(x_61, 6);
x_79 = lean_ctor_get_uint8(x_61, 7);
x_80 = lean_ctor_get_uint8(x_61, 8);
x_81 = lean_ctor_get_uint8(x_61, 10);
x_82 = lean_ctor_get_uint8(x_61, 11);
x_83 = lean_ctor_get_uint8(x_61, 12);
x_84 = lean_ctor_get_uint8(x_61, 13);
x_85 = lean_ctor_get_uint8(x_61, 14);
x_86 = lean_ctor_get_uint8(x_61, 15);
x_87 = lean_ctor_get_uint8(x_61, 16);
x_88 = lean_ctor_get_uint8(x_61, 17);
x_89 = lean_ctor_get_uint8(x_61, 18);
if (lean_is_exclusive(x_61)) {
 x_90 = x_61;
} else {
 lean_dec_ref(x_61);
 x_90 = lean_box(0);
}
x_91 = lean_unsigned_to_nat(1u);
x_92 = l_Lean_Syntax_getArg(x_1, x_91);
x_93 = 2;
if (lean_is_scalar(x_90)) {
 x_94 = lean_alloc_ctor(0, 0, 19);
} else {
 x_94 = x_90;
}
lean_ctor_set_uint8(x_94, 0, x_72);
lean_ctor_set_uint8(x_94, 1, x_73);
lean_ctor_set_uint8(x_94, 2, x_74);
lean_ctor_set_uint8(x_94, 3, x_75);
lean_ctor_set_uint8(x_94, 4, x_76);
lean_ctor_set_uint8(x_94, 5, x_77);
lean_ctor_set_uint8(x_94, 6, x_78);
lean_ctor_set_uint8(x_94, 7, x_79);
lean_ctor_set_uint8(x_94, 8, x_80);
lean_ctor_set_uint8(x_94, 9, x_93);
lean_ctor_set_uint8(x_94, 10, x_81);
lean_ctor_set_uint8(x_94, 11, x_82);
lean_ctor_set_uint8(x_94, 12, x_83);
lean_ctor_set_uint8(x_94, 13, x_84);
lean_ctor_set_uint8(x_94, 14, x_85);
lean_ctor_set_uint8(x_94, 15, x_86);
lean_ctor_set_uint8(x_94, 16, x_87);
lean_ctor_set_uint8(x_94, 17, x_88);
lean_ctor_set_uint8(x_94, 18, x_89);
x_95 = 2;
x_96 = lean_uint64_shift_right(x_62, x_95);
x_97 = lean_uint64_shift_left(x_96, x_95);
x_98 = l_Lean_Elab_Tactic_evalWithReducible___closed__0;
x_99 = lean_uint64_lor(x_97, x_98);
x_100 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_64);
lean_ctor_set(x_100, 2, x_65);
lean_ctor_set(x_100, 3, x_66);
lean_ctor_set(x_100, 4, x_67);
lean_ctor_set(x_100, 5, x_68);
lean_ctor_set(x_100, 6, x_69);
lean_ctor_set_uint64(x_100, sizeof(void*)*7, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 8, x_63);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 9, x_70);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 10, x_71);
x_101 = l_Lean_Elab_Tactic_evalTactic(x_92, x_2, x_3, x_4, x_5, x_100, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
else
{
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalWithReducible(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withReducible", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalWithReducible", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducible___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = lean_unsigned_to_nat(314u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(36u);
x_2 = lean_unsigned_to_nat(315u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(36u);
x_2 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(51u);
x_4 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(55u);
x_2 = lean_unsigned_to_nat(314u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(72u);
x_2 = lean_unsigned_to_nat(314u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(72u);
x_2 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(55u);
x_4 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 3;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint64_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; lean_object* x_23; 
x_14 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = 3;
lean_ctor_set_uint8(x_12, 9, x_17);
x_18 = 2;
x_19 = lean_uint64_shift_right(x_14, x_18);
x_20 = lean_uint64_shift_left(x_19, x_18);
x_21 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0;
x_22 = lean_uint64_lor(x_20, x_21);
lean_ctor_set_uint64(x_6, sizeof(void*)*7, x_22);
x_23 = l_Lean_Elab_Tactic_evalTactic(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
return x_23;
}
}
else
{
uint64_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; lean_object* x_56; 
x_28 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_29 = lean_ctor_get_uint8(x_12, 0);
x_30 = lean_ctor_get_uint8(x_12, 1);
x_31 = lean_ctor_get_uint8(x_12, 2);
x_32 = lean_ctor_get_uint8(x_12, 3);
x_33 = lean_ctor_get_uint8(x_12, 4);
x_34 = lean_ctor_get_uint8(x_12, 5);
x_35 = lean_ctor_get_uint8(x_12, 6);
x_36 = lean_ctor_get_uint8(x_12, 7);
x_37 = lean_ctor_get_uint8(x_12, 8);
x_38 = lean_ctor_get_uint8(x_12, 10);
x_39 = lean_ctor_get_uint8(x_12, 11);
x_40 = lean_ctor_get_uint8(x_12, 12);
x_41 = lean_ctor_get_uint8(x_12, 13);
x_42 = lean_ctor_get_uint8(x_12, 14);
x_43 = lean_ctor_get_uint8(x_12, 15);
x_44 = lean_ctor_get_uint8(x_12, 16);
x_45 = lean_ctor_get_uint8(x_12, 17);
x_46 = lean_ctor_get_uint8(x_12, 18);
lean_dec(x_12);
x_47 = lean_unsigned_to_nat(1u);
x_48 = l_Lean_Syntax_getArg(x_1, x_47);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_50, 0, x_29);
lean_ctor_set_uint8(x_50, 1, x_30);
lean_ctor_set_uint8(x_50, 2, x_31);
lean_ctor_set_uint8(x_50, 3, x_32);
lean_ctor_set_uint8(x_50, 4, x_33);
lean_ctor_set_uint8(x_50, 5, x_34);
lean_ctor_set_uint8(x_50, 6, x_35);
lean_ctor_set_uint8(x_50, 7, x_36);
lean_ctor_set_uint8(x_50, 8, x_37);
lean_ctor_set_uint8(x_50, 9, x_49);
lean_ctor_set_uint8(x_50, 10, x_38);
lean_ctor_set_uint8(x_50, 11, x_39);
lean_ctor_set_uint8(x_50, 12, x_40);
lean_ctor_set_uint8(x_50, 13, x_41);
lean_ctor_set_uint8(x_50, 14, x_42);
lean_ctor_set_uint8(x_50, 15, x_43);
lean_ctor_set_uint8(x_50, 16, x_44);
lean_ctor_set_uint8(x_50, 17, x_45);
lean_ctor_set_uint8(x_50, 18, x_46);
x_51 = 2;
x_52 = lean_uint64_shift_right(x_28, x_51);
x_53 = lean_uint64_shift_left(x_52, x_51);
x_54 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0;
x_55 = lean_uint64_lor(x_53, x_54);
lean_ctor_set(x_6, 0, x_50);
lean_ctor_set_uint64(x_6, sizeof(void*)*7, x_55);
x_56 = l_Lean_Elab_Tactic_evalTactic(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
return x_56;
}
}
}
else
{
lean_object* x_61; uint64_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; lean_object* x_100; lean_object* x_101; 
x_61 = lean_ctor_get(x_6, 0);
x_62 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_63 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_64 = lean_ctor_get(x_6, 1);
x_65 = lean_ctor_get(x_6, 2);
x_66 = lean_ctor_get(x_6, 3);
x_67 = lean_ctor_get(x_6, 4);
x_68 = lean_ctor_get(x_6, 5);
x_69 = lean_ctor_get(x_6, 6);
x_70 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_71 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_61);
lean_dec(x_6);
x_72 = lean_ctor_get_uint8(x_61, 0);
x_73 = lean_ctor_get_uint8(x_61, 1);
x_74 = lean_ctor_get_uint8(x_61, 2);
x_75 = lean_ctor_get_uint8(x_61, 3);
x_76 = lean_ctor_get_uint8(x_61, 4);
x_77 = lean_ctor_get_uint8(x_61, 5);
x_78 = lean_ctor_get_uint8(x_61, 6);
x_79 = lean_ctor_get_uint8(x_61, 7);
x_80 = lean_ctor_get_uint8(x_61, 8);
x_81 = lean_ctor_get_uint8(x_61, 10);
x_82 = lean_ctor_get_uint8(x_61, 11);
x_83 = lean_ctor_get_uint8(x_61, 12);
x_84 = lean_ctor_get_uint8(x_61, 13);
x_85 = lean_ctor_get_uint8(x_61, 14);
x_86 = lean_ctor_get_uint8(x_61, 15);
x_87 = lean_ctor_get_uint8(x_61, 16);
x_88 = lean_ctor_get_uint8(x_61, 17);
x_89 = lean_ctor_get_uint8(x_61, 18);
if (lean_is_exclusive(x_61)) {
 x_90 = x_61;
} else {
 lean_dec_ref(x_61);
 x_90 = lean_box(0);
}
x_91 = lean_unsigned_to_nat(1u);
x_92 = l_Lean_Syntax_getArg(x_1, x_91);
x_93 = 3;
if (lean_is_scalar(x_90)) {
 x_94 = lean_alloc_ctor(0, 0, 19);
} else {
 x_94 = x_90;
}
lean_ctor_set_uint8(x_94, 0, x_72);
lean_ctor_set_uint8(x_94, 1, x_73);
lean_ctor_set_uint8(x_94, 2, x_74);
lean_ctor_set_uint8(x_94, 3, x_75);
lean_ctor_set_uint8(x_94, 4, x_76);
lean_ctor_set_uint8(x_94, 5, x_77);
lean_ctor_set_uint8(x_94, 6, x_78);
lean_ctor_set_uint8(x_94, 7, x_79);
lean_ctor_set_uint8(x_94, 8, x_80);
lean_ctor_set_uint8(x_94, 9, x_93);
lean_ctor_set_uint8(x_94, 10, x_81);
lean_ctor_set_uint8(x_94, 11, x_82);
lean_ctor_set_uint8(x_94, 12, x_83);
lean_ctor_set_uint8(x_94, 13, x_84);
lean_ctor_set_uint8(x_94, 14, x_85);
lean_ctor_set_uint8(x_94, 15, x_86);
lean_ctor_set_uint8(x_94, 16, x_87);
lean_ctor_set_uint8(x_94, 17, x_88);
lean_ctor_set_uint8(x_94, 18, x_89);
x_95 = 2;
x_96 = lean_uint64_shift_right(x_62, x_95);
x_97 = lean_uint64_shift_left(x_96, x_95);
x_98 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0;
x_99 = lean_uint64_lor(x_97, x_98);
x_100 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_64);
lean_ctor_set(x_100, 2, x_65);
lean_ctor_set(x_100, 3, x_66);
lean_ctor_set(x_100, 4, x_67);
lean_ctor_set(x_100, 5, x_68);
lean_ctor_set(x_100, 6, x_69);
lean_ctor_set_uint64(x_100, sizeof(void*)*7, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 8, x_63);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 9, x_70);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 10, x_71);
x_101 = l_Lean_Elab_Tactic_evalTactic(x_92, x_2, x_3, x_4, x_5, x_100, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
else
{
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withReducibleAndInstances", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalWithReducibleAndInstances", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(63u);
x_2 = lean_unsigned_to_nat(317u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(48u);
x_2 = lean_unsigned_to_nat(318u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(48u);
x_2 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(63u);
x_4 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(67u);
x_2 = lean_unsigned_to_nat(317u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(96u);
x_2 = lean_unsigned_to_nat(317u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(96u);
x_2 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(67u);
x_4 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint64_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; lean_object* x_23; 
x_14 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_15 = 0;
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_ctor_set_uint8(x_12, 9, x_15);
x_18 = 2;
x_19 = lean_uint64_shift_right(x_14, x_18);
x_20 = lean_uint64_shift_left(x_19, x_18);
x_21 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0;
x_22 = lean_uint64_lor(x_20, x_21);
lean_ctor_set_uint64(x_6, sizeof(void*)*7, x_22);
x_23 = l_Lean_Elab_Tactic_evalTactic(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
return x_23;
}
}
else
{
uint64_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; lean_object* x_56; 
x_28 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_29 = lean_ctor_get_uint8(x_12, 0);
x_30 = lean_ctor_get_uint8(x_12, 1);
x_31 = lean_ctor_get_uint8(x_12, 2);
x_32 = lean_ctor_get_uint8(x_12, 3);
x_33 = lean_ctor_get_uint8(x_12, 4);
x_34 = lean_ctor_get_uint8(x_12, 5);
x_35 = lean_ctor_get_uint8(x_12, 6);
x_36 = lean_ctor_get_uint8(x_12, 7);
x_37 = lean_ctor_get_uint8(x_12, 8);
x_38 = lean_ctor_get_uint8(x_12, 10);
x_39 = lean_ctor_get_uint8(x_12, 11);
x_40 = lean_ctor_get_uint8(x_12, 12);
x_41 = lean_ctor_get_uint8(x_12, 13);
x_42 = lean_ctor_get_uint8(x_12, 14);
x_43 = lean_ctor_get_uint8(x_12, 15);
x_44 = lean_ctor_get_uint8(x_12, 16);
x_45 = lean_ctor_get_uint8(x_12, 17);
x_46 = lean_ctor_get_uint8(x_12, 18);
lean_dec(x_12);
x_47 = 0;
x_48 = lean_unsigned_to_nat(1u);
x_49 = l_Lean_Syntax_getArg(x_1, x_48);
x_50 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_50, 0, x_29);
lean_ctor_set_uint8(x_50, 1, x_30);
lean_ctor_set_uint8(x_50, 2, x_31);
lean_ctor_set_uint8(x_50, 3, x_32);
lean_ctor_set_uint8(x_50, 4, x_33);
lean_ctor_set_uint8(x_50, 5, x_34);
lean_ctor_set_uint8(x_50, 6, x_35);
lean_ctor_set_uint8(x_50, 7, x_36);
lean_ctor_set_uint8(x_50, 8, x_37);
lean_ctor_set_uint8(x_50, 9, x_47);
lean_ctor_set_uint8(x_50, 10, x_38);
lean_ctor_set_uint8(x_50, 11, x_39);
lean_ctor_set_uint8(x_50, 12, x_40);
lean_ctor_set_uint8(x_50, 13, x_41);
lean_ctor_set_uint8(x_50, 14, x_42);
lean_ctor_set_uint8(x_50, 15, x_43);
lean_ctor_set_uint8(x_50, 16, x_44);
lean_ctor_set_uint8(x_50, 17, x_45);
lean_ctor_set_uint8(x_50, 18, x_46);
x_51 = 2;
x_52 = lean_uint64_shift_right(x_28, x_51);
x_53 = lean_uint64_shift_left(x_52, x_51);
x_54 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0;
x_55 = lean_uint64_lor(x_53, x_54);
lean_ctor_set(x_6, 0, x_50);
lean_ctor_set_uint64(x_6, sizeof(void*)*7, x_55);
x_56 = l_Lean_Elab_Tactic_evalTactic(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
return x_56;
}
}
}
else
{
lean_object* x_61; uint64_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; lean_object* x_100; lean_object* x_101; 
x_61 = lean_ctor_get(x_6, 0);
x_62 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_63 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_64 = lean_ctor_get(x_6, 1);
x_65 = lean_ctor_get(x_6, 2);
x_66 = lean_ctor_get(x_6, 3);
x_67 = lean_ctor_get(x_6, 4);
x_68 = lean_ctor_get(x_6, 5);
x_69 = lean_ctor_get(x_6, 6);
x_70 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_71 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_61);
lean_dec(x_6);
x_72 = lean_ctor_get_uint8(x_61, 0);
x_73 = lean_ctor_get_uint8(x_61, 1);
x_74 = lean_ctor_get_uint8(x_61, 2);
x_75 = lean_ctor_get_uint8(x_61, 3);
x_76 = lean_ctor_get_uint8(x_61, 4);
x_77 = lean_ctor_get_uint8(x_61, 5);
x_78 = lean_ctor_get_uint8(x_61, 6);
x_79 = lean_ctor_get_uint8(x_61, 7);
x_80 = lean_ctor_get_uint8(x_61, 8);
x_81 = lean_ctor_get_uint8(x_61, 10);
x_82 = lean_ctor_get_uint8(x_61, 11);
x_83 = lean_ctor_get_uint8(x_61, 12);
x_84 = lean_ctor_get_uint8(x_61, 13);
x_85 = lean_ctor_get_uint8(x_61, 14);
x_86 = lean_ctor_get_uint8(x_61, 15);
x_87 = lean_ctor_get_uint8(x_61, 16);
x_88 = lean_ctor_get_uint8(x_61, 17);
x_89 = lean_ctor_get_uint8(x_61, 18);
if (lean_is_exclusive(x_61)) {
 x_90 = x_61;
} else {
 lean_dec_ref(x_61);
 x_90 = lean_box(0);
}
x_91 = 0;
x_92 = lean_unsigned_to_nat(1u);
x_93 = l_Lean_Syntax_getArg(x_1, x_92);
if (lean_is_scalar(x_90)) {
 x_94 = lean_alloc_ctor(0, 0, 19);
} else {
 x_94 = x_90;
}
lean_ctor_set_uint8(x_94, 0, x_72);
lean_ctor_set_uint8(x_94, 1, x_73);
lean_ctor_set_uint8(x_94, 2, x_74);
lean_ctor_set_uint8(x_94, 3, x_75);
lean_ctor_set_uint8(x_94, 4, x_76);
lean_ctor_set_uint8(x_94, 5, x_77);
lean_ctor_set_uint8(x_94, 6, x_78);
lean_ctor_set_uint8(x_94, 7, x_79);
lean_ctor_set_uint8(x_94, 8, x_80);
lean_ctor_set_uint8(x_94, 9, x_91);
lean_ctor_set_uint8(x_94, 10, x_81);
lean_ctor_set_uint8(x_94, 11, x_82);
lean_ctor_set_uint8(x_94, 12, x_83);
lean_ctor_set_uint8(x_94, 13, x_84);
lean_ctor_set_uint8(x_94, 14, x_85);
lean_ctor_set_uint8(x_94, 15, x_86);
lean_ctor_set_uint8(x_94, 16, x_87);
lean_ctor_set_uint8(x_94, 17, x_88);
lean_ctor_set_uint8(x_94, 18, x_89);
x_95 = 2;
x_96 = lean_uint64_shift_right(x_62, x_95);
x_97 = lean_uint64_shift_left(x_96, x_95);
x_98 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0;
x_99 = lean_uint64_lor(x_97, x_98);
x_100 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_64);
lean_ctor_set(x_100, 2, x_65);
lean_ctor_set(x_100, 3, x_66);
lean_ctor_set(x_100, 4, x_67);
lean_ctor_set(x_100, 5, x_68);
lean_ctor_set(x_100, 6, x_69);
lean_ctor_set_uint64(x_100, sizeof(void*)*7, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 8, x_63);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 9, x_70);
lean_ctor_set_uint8(x_100, sizeof(void*)*7 + 10, x_71);
x_101 = l_Lean_Elab_Tactic_evalTactic(x_93, x_2, x_3, x_4, x_5, x_100, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
else
{
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalWithUnfoldingAll(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withUnfoldingAll", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalWithUnfoldingAll", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(54u);
x_2 = lean_unsigned_to_nat(320u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(60u);
x_2 = lean_unsigned_to_nat(321u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(60u);
x_2 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(54u);
x_4 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(58u);
x_2 = lean_unsigned_to_nat(320u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(78u);
x_2 = lean_unsigned_to_nat(320u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(78u);
x_2 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(58u);
x_4 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_6);
x_14 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec_ref(x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_15);
x_23 = lean_infer_type(x_15, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_80; 
x_80 = l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1;
x_26 = x_80;
x_27 = x_3;
x_28 = x_6;
x_29 = x_9;
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
goto block_79;
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_4, 0);
lean_inc(x_81);
lean_dec(x_4);
x_82 = 1;
x_26 = x_81;
x_27 = x_82;
x_28 = x_6;
x_29 = x_9;
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
goto block_79;
}
block_79:
{
lean_object* x_33; 
x_33 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_28, x_29, x_30, x_31, x_32, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
x_36 = l_Lean_MVarId_assert(x_34, x_26, x_24, x_15, x_29, x_30, x_31, x_32, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_30);
lean_inc_ref(x_29);
x_39 = l_Lean_Meta_intro1Core(x_37, x_27, x_29, x_30, x_31, x_32, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
x_45 = lean_box(0);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_45);
lean_ctor_set(x_40, 0, x_44);
x_46 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_40, x_28, x_29, x_30, x_31, x_32, x_41);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_43);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_43);
x_51 = !lean_is_exclusive(x_46);
if (x_51 == 0)
{
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_40, 0);
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_40);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_58, x_28, x_29, x_30, x_31, x_32, x_41);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_65 = x_59;
} else {
 lean_dec_ref(x_59);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
x_67 = !lean_is_exclusive(x_39);
if (x_67 == 0)
{
return x_39;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_39, 0);
x_69 = lean_ctor_get(x_39, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_39);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
x_71 = !lean_is_exclusive(x_36);
if (x_71 == 0)
{
return x_36;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_36, 0);
x_73 = lean_ctor_get(x_36, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_36);
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
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_15);
x_75 = !lean_is_exclusive(x_33);
if (x_75 == 0)
{
return x_33;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_33, 0);
x_77 = lean_ctor_get(x_33, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_33);
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
uint8_t x_83; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_23);
if (x_83 == 0)
{
return x_23;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_23, 0);
x_85 = lean_ctor_get(x_23, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_23);
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
uint8_t x_87; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_14);
if (x_87 == 0)
{
return x_14;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_14, 0);
x_89 = lean_ctor_get(x_14, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_14);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(0);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed), 13, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_2);
x_16 = l_Lean_Elab_Tactic_withMainContext___redArg(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
x_15 = l_Lean_Elab_Tactic_elabAsFVar___lam__0(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_4, x_15);
if (x_16 == 1)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_4, x_19);
lean_dec(x_4);
x_21 = lean_array_fget(x_3, x_20);
if (lean_obj_tag(x_21) == 0)
{
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_39; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_39 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_39);
x_24 = x_39;
goto block_38;
block_38:
{
lean_object* x_25; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_25 = l_Lean_Meta_isExprDefEq(x_1, x_24, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Lean_LocalDecl_isImplementationDetail(x_23);
if (x_28 == 0)
{
if (x_2 == 0)
{
lean_dec(x_26);
lean_dec(x_23);
x_4 = x_20;
x_9 = x_27;
goto _start;
}
else
{
uint8_t x_30; 
x_30 = lean_unbox(x_26);
lean_dec(x_26);
if (x_30 == 0)
{
lean_dec(x_23);
x_4 = x_20;
x_9 = x_27;
goto _start;
}
else
{
lean_object* x_32; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_10 = x_27;
x_11 = x_32;
goto block_14;
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_23);
x_4 = x_20;
x_9 = x_27;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_4, x_14);
if (x_15 == 1)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_4);
lean_dec_ref(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_4, x_18);
lean_dec(x_4);
x_20 = lean_array_fget(x_3, x_19);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_1);
x_21 = l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1(x_1, x_2, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_4 = x_19;
x_13 = x_23;
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
return x_21;
}
}
else
{
lean_dec(x_19);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_array_get_size(x_13);
x_15 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_array_get_size(x_16);
x_18 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_16, x_17, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_array_get_size(x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_16 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_14, x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_19;
}
else
{
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_16;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 1);
x_14 = l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___redArg___lam__0), 10, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___redArg(x_2, x_12, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_14 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg___lam__0(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_16);
lean_dec_ref(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_15);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec_ref(x_14);
x_25 = lean_box(0);
x_26 = l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg___lam__0(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25, x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_23);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to find a hypothesis with type", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_13 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_8, 2);
lean_inc_ref(x_16);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_14);
x_17 = l_Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0(x_14, x_3, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__1;
x_21 = l_Lean_indentExpr(x_14);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_24, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec(x_18);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
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
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_4);
x_12 = l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_4, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Lean_Syntax_getId(x_2);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_19 = l_Lean_MVarId_rename(x_16, x_13, x_18, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_23, x_4, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rename", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalRename___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRename___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalRename___closed__1;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Tactic_evalRename___closed__3;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_liftMacroM___at___Lean_Elab_Tactic_evalTactic_expandEval_spec__0_spec__2___redArg(x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_box(x_17);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__0___boxed), 12, 3);
lean_closure_set(x_23, 0, x_20);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover), 11, 2);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, x_23);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___boxed), 12, 3);
lean_closure_set(x_27, 0, lean_box(0));
lean_closure_set(x_27, 1, x_24);
lean_closure_set(x_27, 2, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lam__1___boxed), 11, 2);
lean_closure_set(x_28, 0, x_27);
lean_closure_set(x_28, 1, x_15);
x_29 = l_Lean_Elab_Tactic_withMainContext___redArg(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
x_16 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__0(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1___redArg(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
x_16 = l_Array_findSomeRevM_x3f_find___at___Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1_spec__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l_Lean_PersistentArray_findSomeRevMAux___at___Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0_spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l_Lean_PersistentArray_findSomeRevM_x3f___at___Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0_spec__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
x_14 = l_Lean_LocalContext_findDeclRevM_x3f___at___Lean_Elab_Tactic_evalRename_spec__0(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
x_13 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Elab_Tactic_evalRename_spec__5(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_withoutModifyingState___at___Lean_Elab_Tactic_evalRename_spec__6___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Elab_Tactic_evalRename___lam__0(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalRename___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalRename", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalRename___closed__1;
x_4 = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(44u);
x_2 = lean_unsigned_to_nat(344u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(359u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(44u);
x_4 = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(48u);
x_2 = lean_unsigned_to_nat(344u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(58u);
x_2 = lean_unsigned_to_nat(344u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(58u);
x_2 = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(48u);
x_4 = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1;
x_3 = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected type must not contain free variables", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nUse the '+revert' option to automatically cleanup and revert free variables.", 77, 77);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected type must not contain meta variables", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = l_Lean_instantiateMVars___at___Lean_Elab_Term_MVarErrorInfo_logError_spec__0___redArg(x_1, x_5, x_8);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Lean_Expr_hasFVar(x_42);
if (x_44 == 0)
{
x_9 = x_42;
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_43;
goto block_40;
}
else
{
lean_object* x_45; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_45 = l_Lean_Meta_zetaReduce(x_42, x_4, x_5, x_6, x_7, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_9 = x_46;
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_6;
x_15 = x_7;
x_16 = x_47;
goto block_40;
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_45;
}
}
block_40:
{
uint8_t x_17; 
x_17 = l_Lean_Expr_hasMVar(x_9);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Expr_hasFVar(x_9);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1;
x_21 = l_Lean_indentExpr(x_9);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5;
x_31 = l_Lean_indentExpr(x_9);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_34, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isTrue", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__3;
x_2 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isFalse", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__5;
x_2 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = l_Lean_instInhabitedExpr;
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_22, x_24);
x_26 = lean_nat_add(x_25, x_8);
lean_dec(x_25);
x_27 = lean_array_get(x_23, x_2, x_26);
lean_dec(x_26);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_27);
x_28 = lean_infer_type(x_27, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_31 = l_Lean_Meta_isClass_x3f(x_29, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__2;
x_35 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Name_isMetaprogramming_spec__0(x_32, x_34);
lean_dec(x_32);
if (x_35 == 0)
{
lean_dec_ref(x_27);
lean_inc_ref(x_3);
x_14 = x_3;
x_15 = x_33;
goto block_21;
}
else
{
lean_object* x_36; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_36 = lean_whnf(x_27, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_55; lean_object* x_57; uint8_t x_58; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_57 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__4;
x_58 = l_Lean_Expr_isAppOf(x_37, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__6;
x_60 = l_Lean_Expr_isAppOf(x_37, x_59);
x_55 = x_60;
goto block_56;
}
else
{
x_55 = x_6;
goto block_56;
}
block_54:
{
if (x_39 == 0)
{
lean_dec(x_37);
lean_inc_ref(x_3);
x_14 = x_3;
x_15 = x_38;
goto block_21;
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec_ref(x_3);
x_40 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_37, x_9, x_10, x_11, x_12, x_38);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_40);
if (x_50 == 0)
{
return x_40;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_40, 0);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_40);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
block_56:
{
if (x_55 == 0)
{
x_39 = x_35;
goto block_54;
}
else
{
x_39 = x_5;
goto block_54;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_61 = !lean_is_exclusive(x_36);
if (x_61 == 0)
{
return x_36;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_36, 0);
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_36);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec_ref(x_27);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_65 = !lean_is_exclusive(x_31);
if (x_65 == 0)
{
return x_31;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_31, 0);
x_67 = lean_ctor_get(x_31, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_31);
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
lean_dec_ref(x_27);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_3);
x_69 = !lean_is_exclusive(x_28);
if (x_69 == 0)
{
return x_28;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_28, 0);
x_71 = lean_ctor_get(x_28, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_28);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
block_21:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_8, x_16);
lean_dec(x_8);
x_18 = lean_nat_dec_lt(x_17, x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_dec_ref(x_14);
x_8 = x_17;
x_13 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; 
x_22 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_14, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = l_Lean_instInhabitedExpr;
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_24, x_26);
x_28 = lean_nat_add(x_27, x_10);
lean_dec(x_27);
x_29 = lean_array_get(x_25, x_2, x_28);
lean_dec(x_28);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_29);
x_30 = lean_infer_type(x_29, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_33 = l_Lean_Meta_isClass_x3f(x_31, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__2;
x_37 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Name_isMetaprogramming_spec__0(x_34, x_36);
lean_dec(x_34);
if (x_37 == 0)
{
lean_dec_ref(x_29);
lean_inc_ref(x_3);
x_16 = x_3;
x_17 = x_35;
goto block_23;
}
else
{
lean_object* x_38; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_38 = lean_whnf(x_29, x_11, x_12, x_13, x_14, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_57; lean_object* x_59; uint8_t x_60; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_59 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__4;
x_60 = l_Lean_Expr_isAppOf(x_39, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__6;
x_62 = l_Lean_Expr_isAppOf(x_39, x_61);
x_57 = x_62;
goto block_58;
}
else
{
x_57 = x_6;
goto block_58;
}
block_56:
{
if (x_41 == 0)
{
lean_dec(x_39);
lean_inc_ref(x_3);
x_16 = x_3;
x_17 = x_40;
goto block_23;
}
else
{
lean_object* x_42; 
lean_dec_ref(x_3);
x_42 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_39, x_11, x_12, x_13, x_14, x_40);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_4);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
block_58:
{
if (x_57 == 0)
{
x_41 = x_37;
goto block_56;
}
else
{
x_41 = x_5;
goto block_56;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_3);
x_63 = !lean_is_exclusive(x_38);
if (x_63 == 0)
{
return x_38;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_38, 0);
x_65 = lean_ctor_get(x_38, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_38);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec_ref(x_29);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_3);
x_67 = !lean_is_exclusive(x_33);
if (x_67 == 0)
{
return x_33;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_33, 0);
x_69 = lean_ctor_get(x_33, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_33);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec_ref(x_29);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_3);
x_71 = !lean_is_exclusive(x_30);
if (x_71 == 0)
{
return x_30;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_30, 0);
x_73 = lean_ctor_get(x_30, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_30);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_10, x_18);
x_20 = lean_nat_dec_lt(x_19, x_8);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_16);
x_22 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_19, x_11, x_12, x_13, x_14, x_17);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; 
x_22 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_14, x_17, x_18, x_19, x_20, x_21);
return x_22;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0;
x_2 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
x_12 = lean_ctor_get(x_4, 4);
x_13 = lean_ctor_get(x_4, 5);
x_14 = lean_ctor_get(x_4, 6);
x_15 = lean_ctor_get(x_4, 7);
x_16 = lean_ctor_get(x_4, 8);
x_17 = lean_ctor_get(x_4, 9);
x_18 = lean_ctor_get(x_4, 10);
x_19 = lean_ctor_get(x_4, 11);
x_20 = lean_ctor_get(x_4, 12);
x_21 = lean_nat_dec_eq(x_11, x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_11, x_22);
lean_dec(x_11);
lean_ctor_set(x_4, 3, x_23);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_24 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
x_27 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1;
x_28 = lean_unsigned_to_nat(5u);
x_29 = l_Lean_Expr_isAppOfArity(x_25, x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = l_Lean_Expr_getAppFn(x_25);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_31, x_5, x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec_ref(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
lean_ctor_set(x_32, 0, x_25);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_32, 1);
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = l_Lean_Expr_getAppNumArgs(x_25);
x_43 = l_Lean_Meta_Match_MatcherInfo_arity(x_41);
x_44 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_32, 0, x_25);
return x_32;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_lt(x_46, x_45);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_32, 0, x_25);
return x_32;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_32);
x_48 = lean_box(0);
x_49 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2;
x_50 = 0;
x_51 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3;
lean_inc(x_42);
x_52 = lean_mk_array(x_42, x_51);
x_53 = lean_nat_sub(x_42, x_22);
lean_dec(x_42);
lean_inc(x_25);
x_54 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_25, x_52, x_53);
x_55 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(x_41, x_54, x_49, x_48, x_21, x_44, x_50, x_45, x_46, x_46, x_2, x_3, x_4, x_5, x_39);
lean_dec(x_45);
lean_dec_ref(x_54);
lean_dec(x_41);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_55, 0);
lean_dec(x_59);
lean_ctor_set(x_55, 0, x_25);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_25);
x_62 = !lean_is_exclusive(x_55);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_55, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_64);
return x_55;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_dec(x_55);
x_66 = lean_ctor_get(x_57, 0);
lean_inc(x_66);
lean_dec(x_57);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_25);
x_68 = !lean_is_exclusive(x_55);
if (x_68 == 0)
{
return x_55;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_55, 0);
x_70 = lean_ctor_get(x_55, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_55);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_32, 1);
lean_inc(x_72);
lean_dec(x_32);
x_73 = lean_ctor_get(x_33, 0);
lean_inc(x_73);
lean_dec(x_33);
x_74 = l_Lean_Expr_getAppNumArgs(x_25);
x_75 = l_Lean_Meta_Match_MatcherInfo_arity(x_73);
x_76 = lean_nat_dec_eq(x_74, x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec_ref(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_25);
lean_ctor_set(x_77, 1, x_72);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_nat_dec_lt(x_79, x_78);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_73);
lean_dec_ref(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_25);
lean_ctor_set(x_81, 1, x_72);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_box(0);
x_83 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2;
x_84 = 0;
x_85 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3;
lean_inc(x_74);
x_86 = lean_mk_array(x_74, x_85);
x_87 = lean_nat_sub(x_74, x_22);
lean_dec(x_74);
lean_inc(x_25);
x_88 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_25, x_86, x_87);
x_89 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(x_73, x_88, x_83, x_82, x_21, x_76, x_84, x_78, x_79, x_79, x_2, x_3, x_4, x_5, x_72);
lean_dec(x_78);
lean_dec_ref(x_88);
lean_dec(x_73);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_93 = x_89;
} else {
 lean_dec_ref(x_89);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_25);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_25);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_91, 0);
lean_inc(x_97);
lean_dec(x_91);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_25);
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
}
}
}
}
else
{
lean_dec_ref(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_24;
}
}
else
{
lean_object* x_103; 
lean_dec_ref(x_24);
x_103 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_1 = x_103;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec_ref(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_24;
}
}
else
{
lean_object* x_105; 
lean_free_object(x_4);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_105 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(x_13, x_6);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; uint8_t x_121; 
x_106 = lean_ctor_get(x_4, 0);
x_107 = lean_ctor_get(x_4, 1);
x_108 = lean_ctor_get(x_4, 2);
x_109 = lean_ctor_get(x_4, 3);
x_110 = lean_ctor_get(x_4, 4);
x_111 = lean_ctor_get(x_4, 5);
x_112 = lean_ctor_get(x_4, 6);
x_113 = lean_ctor_get(x_4, 7);
x_114 = lean_ctor_get(x_4, 8);
x_115 = lean_ctor_get(x_4, 9);
x_116 = lean_ctor_get(x_4, 10);
x_117 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_118 = lean_ctor_get(x_4, 11);
x_119 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_120 = lean_ctor_get(x_4, 12);
lean_inc(x_120);
lean_inc(x_118);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_4);
x_121 = lean_nat_dec_eq(x_109, x_110);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_add(x_109, x_122);
lean_dec(x_109);
x_124 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_124, 0, x_106);
lean_ctor_set(x_124, 1, x_107);
lean_ctor_set(x_124, 2, x_108);
lean_ctor_set(x_124, 3, x_123);
lean_ctor_set(x_124, 4, x_110);
lean_ctor_set(x_124, 5, x_111);
lean_ctor_set(x_124, 6, x_112);
lean_ctor_set(x_124, 7, x_113);
lean_ctor_set(x_124, 8, x_114);
lean_ctor_set(x_124, 9, x_115);
lean_ctor_set(x_124, 10, x_116);
lean_ctor_set(x_124, 11, x_118);
lean_ctor_set(x_124, 12, x_120);
lean_ctor_set_uint8(x_124, sizeof(void*)*13, x_117);
lean_ctor_set_uint8(x_124, sizeof(void*)*13 + 1, x_119);
lean_inc(x_5);
lean_inc_ref(x_124);
lean_inc(x_3);
lean_inc_ref(x_2);
x_125 = lean_whnf(x_1, x_2, x_3, x_124, x_5, x_6);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
x_128 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1;
x_129 = lean_unsigned_to_nat(5u);
x_130 = l_Lean_Expr_isAppOfArity(x_126, x_128, x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = l_Lean_Expr_getAppFn(x_126);
if (lean_obj_tag(x_131) == 4)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec_ref(x_125);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_132, x_5, x_127);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec_ref(x_124);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_ctor_set(x_137, 0, x_126);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_139 = x_133;
} else {
 lean_dec_ref(x_133);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_134, 0);
lean_inc(x_140);
lean_dec(x_134);
x_141 = l_Lean_Expr_getAppNumArgs(x_126);
x_142 = l_Lean_Meta_Match_MatcherInfo_arity(x_140);
x_143 = lean_nat_dec_eq(x_141, x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec_ref(x_124);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_139)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_139;
}
lean_ctor_set(x_144, 0, x_126);
lean_ctor_set(x_144, 1, x_138);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_lt(x_146, x_145);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_145);
lean_dec(x_141);
lean_dec(x_140);
lean_dec_ref(x_124);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_139)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_139;
}
lean_ctor_set(x_148, 0, x_126);
lean_ctor_set(x_148, 1, x_138);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_139);
x_149 = lean_box(0);
x_150 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2;
x_151 = 0;
x_152 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3;
lean_inc(x_141);
x_153 = lean_mk_array(x_141, x_152);
x_154 = lean_nat_sub(x_141, x_122);
lean_dec(x_141);
lean_inc(x_126);
x_155 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_126, x_153, x_154);
x_156 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(x_140, x_155, x_150, x_149, x_121, x_143, x_151, x_145, x_146, x_146, x_2, x_3, x_124, x_5, x_138);
lean_dec(x_145);
lean_dec_ref(x_155);
lean_dec(x_140);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec(x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_160 = x_156;
} else {
 lean_dec_ref(x_156);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_126);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_126);
x_162 = lean_ctor_get(x_156, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_163 = x_156;
} else {
 lean_dec_ref(x_156);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_158, 0);
lean_inc(x_164);
lean_dec(x_158);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_126);
x_166 = lean_ctor_get(x_156, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_156, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_168 = x_156;
} else {
 lean_dec_ref(x_156);
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
}
}
else
{
lean_dec_ref(x_131);
lean_dec(x_127);
lean_dec(x_126);
lean_dec_ref(x_124);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_125;
}
}
else
{
lean_object* x_170; 
lean_dec_ref(x_125);
x_170 = l_Lean_Expr_appArg_x21(x_126);
lean_dec(x_126);
x_1 = x_170;
x_4 = x_124;
x_6 = x_127;
goto _start;
}
}
else
{
lean_dec_ref(x_124);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_125;
}
}
else
{
lean_object* x_172; 
lean_dec_ref(x_120);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec_ref(x_106);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_172 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_withIncRecDepth___at___Lean_Meta_transformWithCache_visit___at___Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0_spec__0_spec__9_spec__9___redArg(x_111, x_6);
return x_172;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_5);
x_15 = lean_unbox(x_6);
x_16 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___boxed(lean_object** _args) {
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
uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_unbox(x_5);
x_23 = lean_unbox(x_6);
x_24 = lean_unbox(x_7);
x_25 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0(x_1, x_2, x_3, x_4, x_22, x_23, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_5);
x_17 = lean_unbox(x_6);
x_18 = lean_unbox(x_7);
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(x_1, x_2, x_3, x_4, x_16, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___boxed(lean_object** _args) {
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
uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_unbox(x_5);
x_23 = lean_unbox(x_6);
x_24 = lean_unbox(x_7);
x_25 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(x_1, x_2, x_3, x_4, x_22, x_23, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_25;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic '", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' evaluated that the proposition", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nis false", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' failed. Error: ", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' failed, could not evaluate decidable instance. Error: ", 56, 56);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
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
lean_dec_ref(x_5);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1;
x_17 = l_Lean_MessageData_ofName(x_3);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__3;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_indentExpr(x_4);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__5;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1;
x_27 = l_Lean_MessageData_ofName(x_3);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__3;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_indentExpr(x_4);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__5;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec_ref(x_4);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_11, 0);
lean_dec(x_37);
x_38 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1;
x_39 = l_Lean_MessageData_ofName(x_3);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__7;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Exception_toMessageData(x_5);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_11, 0, x_46);
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_dec(x_11);
x_48 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1;
x_49 = l_Lean_MessageData_ofName(x_3);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__7;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Exception_toMessageData(x_5);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_47);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_74; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_58 = lean_ctor_get(x_11, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_60 = x_11;
} else {
 lean_dec_ref(x_11);
 x_60 = lean_box(0);
}
x_74 = l_Lean_Exception_isInterrupt(x_58);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Exception_isRuntime(x_58);
x_61 = x_75;
goto block_73;
}
else
{
x_61 = x_74;
goto block_73;
}
block_73:
{
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_62 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1;
x_63 = l_Lean_MessageData_ofName(x_3);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__9;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Exception_toMessageData(x_58);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_60)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_60;
 lean_ctor_set_tag(x_71, 0);
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_59);
return x_71;
}
else
{
lean_object* x_72; 
lean_dec(x_3);
if (lean_is_scalar(x_60)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_60;
}
lean_ctor_set(x_72, 0, x_58);
lean_ctor_set(x_72, 1, x_59);
return x_72;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_nativeDecide", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__2;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__3;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__4;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__4;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__7;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__8;
x_3 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__13;
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__10;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__17;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__18;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofReduceBool", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__20;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__21;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_async;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__26;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__27;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_11 = l_Lean_Meta_mkDecide(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__1;
x_15 = l_Lean_mkAuxDeclName___at___Lean_Elab_Term_mkAuxName_spec__0___redArg(x_14, x_9, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__9;
lean_inc_ref(x_2);
x_20 = l_Lean_CollectLevelParams_main(x_2, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_20, 2);
x_23 = lean_ctor_get(x_20, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = lean_array_to_list(x_22);
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__12;
lean_inc(x_26);
lean_inc(x_17);
lean_ctor_set(x_20, 2, x_28);
lean_ctor_set(x_20, 1, x_26);
lean_ctor_set(x_20, 0, x_17);
x_29 = lean_box(1);
x_30 = 1;
lean_inc(x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_25);
lean_inc(x_12);
x_31 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_12);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_15);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_inc(x_9);
lean_inc_ref(x_8);
x_33 = l_Lean_addAndCompile(x_32, x_8, x_9, x_18);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__15;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_36 = l_Lean_Meta_mkEqRefl(x_35, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_124; uint8_t x_149; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_9, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_53 = lean_st_ref_get(x_9, x_41);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_8, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_8, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_8, 5);
lean_inc(x_60);
x_61 = lean_ctor_get(x_8, 6);
lean_inc(x_61);
x_62 = lean_ctor_get(x_8, 7);
lean_inc(x_62);
x_63 = lean_ctor_get(x_8, 8);
lean_inc(x_63);
x_64 = lean_ctor_get(x_8, 9);
lean_inc(x_64);
x_65 = lean_ctor_get(x_8, 10);
lean_inc(x_65);
x_66 = lean_ctor_get(x_8, 11);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_68 = lean_ctor_get(x_8, 12);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_69);
lean_dec(x_54);
x_70 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_71 = 1;
lean_inc(x_26);
x_72 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_26, x_27);
x_73 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__19;
x_74 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__22;
lean_inc(x_72);
lean_inc(x_17);
x_75 = l_Lean_Expr_const___override(x_17, x_72);
x_76 = l_Lean_mkApp3(x_74, x_75, x_35, x_37);
lean_inc_ref(x_2);
x_77 = l_Lean_mkApp3(x_73, x_2, x_70, x_76);
x_78 = lean_box(0);
x_79 = 0;
x_80 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__23;
x_81 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_58, x_80, x_79);
x_82 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__24;
x_83 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_81, x_82);
x_149 = l_Lean_Kernel_isDiagnosticsEnabled(x_69);
lean_dec_ref(x_69);
if (x_149 == 0)
{
if (x_83 == 0)
{
lean_inc(x_9);
x_84 = x_56;
x_85 = x_57;
x_86 = x_59;
x_87 = x_60;
x_88 = x_61;
x_89 = x_62;
x_90 = x_63;
x_91 = x_64;
x_92 = x_65;
x_93 = x_66;
x_94 = x_67;
x_95 = x_68;
x_96 = x_9;
x_97 = x_55;
goto block_123;
}
else
{
x_124 = x_149;
goto block_148;
}
}
else
{
x_124 = x_83;
goto block_148;
}
block_52:
{
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_42);
x_46 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_40, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__16;
x_49 = lean_array_push(x_48, x_2);
x_50 = l_Lean_MessageData_ofLazyM(x_44, x_49);
x_51 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_50, x_6, x_7, x_8, x_9, x_47);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_51;
}
else
{
lean_dec(x_44);
lean_dec(x_40);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_42;
}
}
block_123:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__25;
x_99 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_81, x_98);
x_100 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_100, 0, x_84);
lean_ctor_set(x_100, 1, x_85);
lean_ctor_set(x_100, 2, x_81);
lean_ctor_set(x_100, 3, x_86);
lean_ctor_set(x_100, 4, x_99);
lean_ctor_set(x_100, 5, x_87);
lean_ctor_set(x_100, 6, x_88);
lean_ctor_set(x_100, 7, x_89);
lean_ctor_set(x_100, 8, x_90);
lean_ctor_set(x_100, 9, x_91);
lean_ctor_set(x_100, 10, x_92);
lean_ctor_set(x_100, 11, x_93);
lean_ctor_set(x_100, 12, x_95);
lean_ctor_set_uint8(x_100, sizeof(void*)*13, x_83);
lean_ctor_set_uint8(x_100, sizeof(void*)*13 + 1, x_94);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_101 = l_Lean_Meta_mkAuxLemma(x_26, x_2, x_77, x_78, x_71, x_79, x_6, x_7, x_100, x_96, x_97);
if (lean_obj_tag(x_101) == 0)
{
uint8_t x_102; 
lean_dec(x_40);
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = l_Lean_Expr_const___override(x_103, x_72);
lean_ctor_set(x_101, 0, x_104);
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = l_Lean_Expr_const___override(x_105, x_72);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_72);
x_109 = !lean_is_exclusive(x_101);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_110 = lean_ctor_get(x_101, 0);
x_111 = lean_ctor_get(x_101, 1);
x_112 = lean_box(x_71);
lean_inc(x_110);
lean_inc_ref(x_2);
x_113 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_113, 0, x_17);
lean_closure_set(x_113, 1, x_112);
lean_closure_set(x_113, 2, x_1);
lean_closure_set(x_113, 3, x_2);
lean_closure_set(x_113, 4, x_110);
lean_inc(x_111);
lean_inc(x_110);
x_114 = l_Lean_Exception_isInterrupt(x_110);
if (x_114 == 0)
{
uint8_t x_115; 
x_115 = l_Lean_Exception_isRuntime(x_110);
lean_dec(x_110);
x_42 = x_101;
x_43 = x_111;
x_44 = x_113;
x_45 = x_115;
goto block_52;
}
else
{
lean_dec(x_110);
x_42 = x_101;
x_43 = x_111;
x_44 = x_113;
x_45 = x_114;
goto block_52;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_116 = lean_ctor_get(x_101, 0);
x_117 = lean_ctor_get(x_101, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_101);
x_118 = lean_box(x_71);
lean_inc(x_116);
lean_inc_ref(x_2);
x_119 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_119, 0, x_17);
lean_closure_set(x_119, 1, x_118);
lean_closure_set(x_119, 2, x_1);
lean_closure_set(x_119, 3, x_2);
lean_closure_set(x_119, 4, x_116);
lean_inc(x_117);
lean_inc(x_116);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_117);
x_121 = l_Lean_Exception_isInterrupt(x_116);
if (x_121 == 0)
{
uint8_t x_122; 
x_122 = l_Lean_Exception_isRuntime(x_116);
lean_dec(x_116);
x_42 = x_120;
x_43 = x_117;
x_44 = x_119;
x_45 = x_122;
goto block_52;
}
else
{
lean_dec(x_116);
x_42 = x_120;
x_43 = x_117;
x_44 = x_119;
x_45 = x_121;
goto block_52;
}
}
}
}
block_148:
{
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = lean_st_ref_take(x_9, x_55);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = !lean_is_exclusive(x_126);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_126, 0);
x_130 = lean_ctor_get(x_126, 5);
lean_dec(x_130);
x_131 = l_Lean_Kernel_enableDiag(x_129, x_83);
x_132 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28;
lean_ctor_set(x_126, 5, x_132);
lean_ctor_set(x_126, 0, x_131);
x_133 = lean_st_ref_set(x_9, x_126, x_127);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec_ref(x_133);
lean_inc(x_9);
x_84 = x_56;
x_85 = x_57;
x_86 = x_59;
x_87 = x_60;
x_88 = x_61;
x_89 = x_62;
x_90 = x_63;
x_91 = x_64;
x_92 = x_65;
x_93 = x_66;
x_94 = x_67;
x_95 = x_68;
x_96 = x_9;
x_97 = x_134;
goto block_123;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_135 = lean_ctor_get(x_126, 0);
x_136 = lean_ctor_get(x_126, 1);
x_137 = lean_ctor_get(x_126, 2);
x_138 = lean_ctor_get(x_126, 3);
x_139 = lean_ctor_get(x_126, 4);
x_140 = lean_ctor_get(x_126, 6);
x_141 = lean_ctor_get(x_126, 7);
x_142 = lean_ctor_get(x_126, 8);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_126);
x_143 = l_Lean_Kernel_enableDiag(x_135, x_83);
x_144 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28;
x_145 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_136);
lean_ctor_set(x_145, 2, x_137);
lean_ctor_set(x_145, 3, x_138);
lean_ctor_set(x_145, 4, x_139);
lean_ctor_set(x_145, 5, x_144);
lean_ctor_set(x_145, 6, x_140);
lean_ctor_set(x_145, 7, x_141);
lean_ctor_set(x_145, 8, x_142);
x_146 = lean_st_ref_set(x_9, x_145, x_127);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec_ref(x_146);
lean_inc(x_9);
x_84 = x_56;
x_85 = x_57;
x_86 = x_59;
x_87 = x_60;
x_88 = x_61;
x_89 = x_62;
x_90 = x_63;
x_91 = x_64;
x_92 = x_65;
x_93 = x_66;
x_94 = x_67;
x_95 = x_68;
x_96 = x_9;
x_97 = x_147;
goto block_123;
}
}
else
{
lean_inc(x_9);
x_84 = x_56;
x_85 = x_57;
x_86 = x_59;
x_87 = x_60;
x_88 = x_61;
x_89 = x_62;
x_90 = x_63;
x_91 = x_64;
x_92 = x_65;
x_93 = x_66;
x_94 = x_67;
x_95 = x_68;
x_96 = x_9;
x_97 = x_55;
goto block_123;
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_36;
}
}
else
{
uint8_t x_150; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_33);
if (x_150 == 0)
{
return x_33;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_33, 0);
x_152 = lean_ctor_get(x_33, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_33);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = lean_ctor_get(x_20, 2);
lean_inc(x_154);
lean_dec(x_20);
x_155 = lean_box(0);
x_156 = lean_array_to_list(x_154);
x_157 = lean_box(0);
x_158 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__12;
lean_inc(x_156);
lean_inc(x_17);
x_159 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_159, 0, x_17);
lean_ctor_set(x_159, 1, x_156);
lean_ctor_set(x_159, 2, x_158);
x_160 = lean_box(1);
x_161 = 1;
lean_inc(x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 1, x_155);
lean_inc(x_12);
x_162 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_12);
lean_ctor_set(x_162, 2, x_160);
lean_ctor_set(x_162, 3, x_15);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
lean_inc(x_9);
lean_inc_ref(x_8);
x_164 = l_Lean_addAndCompile(x_163, x_8, x_9, x_18);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__15;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_167 = l_Lean_Meta_mkEqRefl(x_166, x_6, x_7, x_8, x_9, x_165);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_247; uint8_t x_266; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec_ref(x_167);
x_170 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_9, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec_ref(x_170);
x_184 = lean_st_ref_get(x_9, x_172);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec_ref(x_184);
x_187 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_187);
x_188 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_8, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_8, 3);
lean_inc(x_190);
x_191 = lean_ctor_get(x_8, 5);
lean_inc(x_191);
x_192 = lean_ctor_get(x_8, 6);
lean_inc(x_192);
x_193 = lean_ctor_get(x_8, 7);
lean_inc(x_193);
x_194 = lean_ctor_get(x_8, 8);
lean_inc(x_194);
x_195 = lean_ctor_get(x_8, 9);
lean_inc(x_195);
x_196 = lean_ctor_get(x_8, 10);
lean_inc(x_196);
x_197 = lean_ctor_get(x_8, 11);
lean_inc(x_197);
x_198 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_199 = lean_ctor_get(x_8, 12);
lean_inc_ref(x_199);
x_200 = lean_ctor_get(x_185, 0);
lean_inc_ref(x_200);
lean_dec(x_185);
x_201 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_202 = 1;
lean_inc(x_156);
x_203 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_156, x_157);
x_204 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__19;
x_205 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__22;
lean_inc(x_203);
lean_inc(x_17);
x_206 = l_Lean_Expr_const___override(x_17, x_203);
x_207 = l_Lean_mkApp3(x_205, x_206, x_166, x_168);
lean_inc_ref(x_2);
x_208 = l_Lean_mkApp3(x_204, x_2, x_201, x_207);
x_209 = lean_box(0);
x_210 = 0;
x_211 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__23;
x_212 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_189, x_211, x_210);
x_213 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__24;
x_214 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_212, x_213);
x_266 = l_Lean_Kernel_isDiagnosticsEnabled(x_200);
lean_dec_ref(x_200);
if (x_266 == 0)
{
if (x_214 == 0)
{
lean_inc(x_9);
x_215 = x_187;
x_216 = x_188;
x_217 = x_190;
x_218 = x_191;
x_219 = x_192;
x_220 = x_193;
x_221 = x_194;
x_222 = x_195;
x_223 = x_196;
x_224 = x_197;
x_225 = x_198;
x_226 = x_199;
x_227 = x_9;
x_228 = x_186;
goto block_246;
}
else
{
x_247 = x_266;
goto block_265;
}
}
else
{
x_247 = x_214;
goto block_265;
}
block_183:
{
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec_ref(x_173);
x_177 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_171, x_176, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_174);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__16;
x_180 = lean_array_push(x_179, x_2);
x_181 = l_Lean_MessageData_ofLazyM(x_175, x_180);
x_182 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_181, x_6, x_7, x_8, x_9, x_178);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_182;
}
else
{
lean_dec(x_175);
lean_dec(x_171);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_173;
}
}
block_246:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__25;
x_230 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_212, x_229);
x_231 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_231, 0, x_215);
lean_ctor_set(x_231, 1, x_216);
lean_ctor_set(x_231, 2, x_212);
lean_ctor_set(x_231, 3, x_217);
lean_ctor_set(x_231, 4, x_230);
lean_ctor_set(x_231, 5, x_218);
lean_ctor_set(x_231, 6, x_219);
lean_ctor_set(x_231, 7, x_220);
lean_ctor_set(x_231, 8, x_221);
lean_ctor_set(x_231, 9, x_222);
lean_ctor_set(x_231, 10, x_223);
lean_ctor_set(x_231, 11, x_224);
lean_ctor_set(x_231, 12, x_226);
lean_ctor_set_uint8(x_231, sizeof(void*)*13, x_214);
lean_ctor_set_uint8(x_231, sizeof(void*)*13 + 1, x_225);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_232 = l_Lean_Meta_mkAuxLemma(x_156, x_2, x_208, x_209, x_202, x_210, x_6, x_7, x_231, x_227, x_228);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_171);
lean_dec(x_17);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
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
x_236 = l_Lean_Expr_const___override(x_233, x_203);
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
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
lean_dec(x_203);
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
x_241 = lean_box(x_202);
lean_inc(x_238);
lean_inc_ref(x_2);
x_242 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_242, 0, x_17);
lean_closure_set(x_242, 1, x_241);
lean_closure_set(x_242, 2, x_1);
lean_closure_set(x_242, 3, x_2);
lean_closure_set(x_242, 4, x_238);
lean_inc(x_239);
lean_inc(x_238);
if (lean_is_scalar(x_240)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_240;
}
lean_ctor_set(x_243, 0, x_238);
lean_ctor_set(x_243, 1, x_239);
x_244 = l_Lean_Exception_isInterrupt(x_238);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = l_Lean_Exception_isRuntime(x_238);
lean_dec(x_238);
x_173 = x_243;
x_174 = x_239;
x_175 = x_242;
x_176 = x_245;
goto block_183;
}
else
{
lean_dec(x_238);
x_173 = x_243;
x_174 = x_239;
x_175 = x_242;
x_176 = x_244;
goto block_183;
}
}
}
block_265:
{
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_248 = lean_st_ref_take(x_9, x_186);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec_ref(x_248);
x_251 = lean_ctor_get(x_249, 0);
lean_inc_ref(x_251);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_249, 2);
lean_inc_ref(x_253);
x_254 = lean_ctor_get(x_249, 3);
lean_inc_ref(x_254);
x_255 = lean_ctor_get(x_249, 4);
lean_inc_ref(x_255);
x_256 = lean_ctor_get(x_249, 6);
lean_inc_ref(x_256);
x_257 = lean_ctor_get(x_249, 7);
lean_inc_ref(x_257);
x_258 = lean_ctor_get(x_249, 8);
lean_inc_ref(x_258);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 lean_ctor_release(x_249, 2);
 lean_ctor_release(x_249, 3);
 lean_ctor_release(x_249, 4);
 lean_ctor_release(x_249, 5);
 lean_ctor_release(x_249, 6);
 lean_ctor_release(x_249, 7);
 lean_ctor_release(x_249, 8);
 x_259 = x_249;
} else {
 lean_dec_ref(x_249);
 x_259 = lean_box(0);
}
x_260 = l_Lean_Kernel_enableDiag(x_251, x_214);
x_261 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28;
if (lean_is_scalar(x_259)) {
 x_262 = lean_alloc_ctor(0, 9, 0);
} else {
 x_262 = x_259;
}
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_252);
lean_ctor_set(x_262, 2, x_253);
lean_ctor_set(x_262, 3, x_254);
lean_ctor_set(x_262, 4, x_255);
lean_ctor_set(x_262, 5, x_261);
lean_ctor_set(x_262, 6, x_256);
lean_ctor_set(x_262, 7, x_257);
lean_ctor_set(x_262, 8, x_258);
x_263 = lean_st_ref_set(x_9, x_262, x_250);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec_ref(x_263);
lean_inc(x_9);
x_215 = x_187;
x_216 = x_188;
x_217 = x_190;
x_218 = x_191;
x_219 = x_192;
x_220 = x_193;
x_221 = x_194;
x_222 = x_195;
x_223 = x_196;
x_224 = x_197;
x_225 = x_198;
x_226 = x_199;
x_227 = x_9;
x_228 = x_264;
goto block_246;
}
else
{
lean_inc(x_9);
x_215 = x_187;
x_216 = x_188;
x_217 = x_190;
x_218 = x_191;
x_219 = x_192;
x_220 = x_193;
x_221 = x_194;
x_222 = x_195;
x_223 = x_196;
x_224 = x_197;
x_225 = x_198;
x_226 = x_199;
x_227 = x_9;
x_228 = x_186;
goto block_246;
}
}
}
else
{
lean_dec(x_156);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_167;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_156);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_267 = lean_ctor_get(x_164, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_164, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_269 = x_164;
} else {
 lean_dec_ref(x_164);
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
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_271 = lean_ctor_get(x_15, 0);
x_272 = lean_ctor_get(x_15, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_15);
x_273 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__9;
lean_inc_ref(x_2);
x_274 = l_Lean_CollectLevelParams_main(x_2, x_273);
x_275 = lean_ctor_get(x_274, 2);
lean_inc_ref(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 lean_ctor_release(x_274, 2);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
x_277 = lean_box(0);
x_278 = lean_array_to_list(x_275);
x_279 = lean_box(0);
x_280 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__12;
lean_inc(x_278);
lean_inc(x_271);
if (lean_is_scalar(x_276)) {
 x_281 = lean_alloc_ctor(0, 3, 0);
} else {
 x_281 = x_276;
}
lean_ctor_set(x_281, 0, x_271);
lean_ctor_set(x_281, 1, x_278);
lean_ctor_set(x_281, 2, x_280);
x_282 = lean_box(1);
x_283 = 1;
lean_inc(x_271);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_271);
lean_ctor_set(x_284, 1, x_277);
lean_inc(x_12);
x_285 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_285, 0, x_281);
lean_ctor_set(x_285, 1, x_12);
lean_ctor_set(x_285, 2, x_282);
lean_ctor_set(x_285, 3, x_284);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_283);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
lean_inc(x_9);
lean_inc_ref(x_8);
x_287 = l_Lean_addAndCompile(x_286, x_8, x_9, x_272);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
lean_dec_ref(x_287);
x_289 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__15;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_290 = l_Lean_Meta_mkEqRefl(x_289, x_6, x_7, x_8, x_9, x_288);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_370; uint8_t x_389; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec_ref(x_290);
x_293 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_9, x_292);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec_ref(x_293);
x_307 = lean_st_ref_get(x_9, x_295);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec_ref(x_307);
x_310 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_310);
x_311 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_311);
x_312 = lean_ctor_get(x_8, 2);
lean_inc(x_312);
x_313 = lean_ctor_get(x_8, 3);
lean_inc(x_313);
x_314 = lean_ctor_get(x_8, 5);
lean_inc(x_314);
x_315 = lean_ctor_get(x_8, 6);
lean_inc(x_315);
x_316 = lean_ctor_get(x_8, 7);
lean_inc(x_316);
x_317 = lean_ctor_get(x_8, 8);
lean_inc(x_317);
x_318 = lean_ctor_get(x_8, 9);
lean_inc(x_318);
x_319 = lean_ctor_get(x_8, 10);
lean_inc(x_319);
x_320 = lean_ctor_get(x_8, 11);
lean_inc(x_320);
x_321 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_322 = lean_ctor_get(x_8, 12);
lean_inc_ref(x_322);
x_323 = lean_ctor_get(x_308, 0);
lean_inc_ref(x_323);
lean_dec(x_308);
x_324 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_325 = 1;
lean_inc(x_278);
x_326 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_278, x_279);
x_327 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__19;
x_328 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__22;
lean_inc(x_326);
lean_inc(x_271);
x_329 = l_Lean_Expr_const___override(x_271, x_326);
x_330 = l_Lean_mkApp3(x_328, x_329, x_289, x_291);
lean_inc_ref(x_2);
x_331 = l_Lean_mkApp3(x_327, x_2, x_324, x_330);
x_332 = lean_box(0);
x_333 = 0;
x_334 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__23;
x_335 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_312, x_334, x_333);
x_336 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__24;
x_337 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_335, x_336);
x_389 = l_Lean_Kernel_isDiagnosticsEnabled(x_323);
lean_dec_ref(x_323);
if (x_389 == 0)
{
if (x_337 == 0)
{
lean_inc(x_9);
x_338 = x_310;
x_339 = x_311;
x_340 = x_313;
x_341 = x_314;
x_342 = x_315;
x_343 = x_316;
x_344 = x_317;
x_345 = x_318;
x_346 = x_319;
x_347 = x_320;
x_348 = x_321;
x_349 = x_322;
x_350 = x_9;
x_351 = x_309;
goto block_369;
}
else
{
x_370 = x_389;
goto block_388;
}
}
else
{
x_370 = x_337;
goto block_388;
}
block_306:
{
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec_ref(x_296);
x_300 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_294, x_299, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_297);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
lean_dec_ref(x_300);
x_302 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__16;
x_303 = lean_array_push(x_302, x_2);
x_304 = l_Lean_MessageData_ofLazyM(x_298, x_303);
x_305 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_304, x_6, x_7, x_8, x_9, x_301);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_305;
}
else
{
lean_dec(x_298);
lean_dec(x_294);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_296;
}
}
block_369:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_352 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__25;
x_353 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_335, x_352);
x_354 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_354, 0, x_338);
lean_ctor_set(x_354, 1, x_339);
lean_ctor_set(x_354, 2, x_335);
lean_ctor_set(x_354, 3, x_340);
lean_ctor_set(x_354, 4, x_353);
lean_ctor_set(x_354, 5, x_341);
lean_ctor_set(x_354, 6, x_342);
lean_ctor_set(x_354, 7, x_343);
lean_ctor_set(x_354, 8, x_344);
lean_ctor_set(x_354, 9, x_345);
lean_ctor_set(x_354, 10, x_346);
lean_ctor_set(x_354, 11, x_347);
lean_ctor_set(x_354, 12, x_349);
lean_ctor_set_uint8(x_354, sizeof(void*)*13, x_337);
lean_ctor_set_uint8(x_354, sizeof(void*)*13 + 1, x_348);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_355 = l_Lean_Meta_mkAuxLemma(x_278, x_2, x_331, x_332, x_325, x_333, x_6, x_7, x_354, x_350, x_351);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_294);
lean_dec(x_271);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_358 = x_355;
} else {
 lean_dec_ref(x_355);
 x_358 = lean_box(0);
}
x_359 = l_Lean_Expr_const___override(x_356, x_326);
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_357);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; 
lean_dec(x_326);
x_361 = lean_ctor_get(x_355, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_355, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_363 = x_355;
} else {
 lean_dec_ref(x_355);
 x_363 = lean_box(0);
}
x_364 = lean_box(x_325);
lean_inc(x_361);
lean_inc_ref(x_2);
x_365 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_365, 0, x_271);
lean_closure_set(x_365, 1, x_364);
lean_closure_set(x_365, 2, x_1);
lean_closure_set(x_365, 3, x_2);
lean_closure_set(x_365, 4, x_361);
lean_inc(x_362);
lean_inc(x_361);
if (lean_is_scalar(x_363)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_363;
}
lean_ctor_set(x_366, 0, x_361);
lean_ctor_set(x_366, 1, x_362);
x_367 = l_Lean_Exception_isInterrupt(x_361);
if (x_367 == 0)
{
uint8_t x_368; 
x_368 = l_Lean_Exception_isRuntime(x_361);
lean_dec(x_361);
x_296 = x_366;
x_297 = x_362;
x_298 = x_365;
x_299 = x_368;
goto block_306;
}
else
{
lean_dec(x_361);
x_296 = x_366;
x_297 = x_362;
x_298 = x_365;
x_299 = x_367;
goto block_306;
}
}
}
block_388:
{
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_371 = lean_st_ref_take(x_9, x_309);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
lean_dec_ref(x_371);
x_374 = lean_ctor_get(x_372, 0);
lean_inc_ref(x_374);
x_375 = lean_ctor_get(x_372, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_372, 2);
lean_inc_ref(x_376);
x_377 = lean_ctor_get(x_372, 3);
lean_inc_ref(x_377);
x_378 = lean_ctor_get(x_372, 4);
lean_inc_ref(x_378);
x_379 = lean_ctor_get(x_372, 6);
lean_inc_ref(x_379);
x_380 = lean_ctor_get(x_372, 7);
lean_inc_ref(x_380);
x_381 = lean_ctor_get(x_372, 8);
lean_inc_ref(x_381);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 lean_ctor_release(x_372, 2);
 lean_ctor_release(x_372, 3);
 lean_ctor_release(x_372, 4);
 lean_ctor_release(x_372, 5);
 lean_ctor_release(x_372, 6);
 lean_ctor_release(x_372, 7);
 lean_ctor_release(x_372, 8);
 x_382 = x_372;
} else {
 lean_dec_ref(x_372);
 x_382 = lean_box(0);
}
x_383 = l_Lean_Kernel_enableDiag(x_374, x_337);
x_384 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28;
if (lean_is_scalar(x_382)) {
 x_385 = lean_alloc_ctor(0, 9, 0);
} else {
 x_385 = x_382;
}
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_375);
lean_ctor_set(x_385, 2, x_376);
lean_ctor_set(x_385, 3, x_377);
lean_ctor_set(x_385, 4, x_378);
lean_ctor_set(x_385, 5, x_384);
lean_ctor_set(x_385, 6, x_379);
lean_ctor_set(x_385, 7, x_380);
lean_ctor_set(x_385, 8, x_381);
x_386 = lean_st_ref_set(x_9, x_385, x_373);
x_387 = lean_ctor_get(x_386, 1);
lean_inc(x_387);
lean_dec_ref(x_386);
lean_inc(x_9);
x_338 = x_310;
x_339 = x_311;
x_340 = x_313;
x_341 = x_314;
x_342 = x_315;
x_343 = x_316;
x_344 = x_317;
x_345 = x_318;
x_346 = x_319;
x_347 = x_320;
x_348 = x_321;
x_349 = x_322;
x_350 = x_9;
x_351 = x_387;
goto block_369;
}
else
{
lean_inc(x_9);
x_338 = x_310;
x_339 = x_311;
x_340 = x_313;
x_341 = x_314;
x_342 = x_315;
x_343 = x_316;
x_344 = x_317;
x_345 = x_318;
x_346 = x_319;
x_347 = x_320;
x_348 = x_321;
x_349 = x_322;
x_350 = x_9;
x_351 = x_309;
goto block_369;
}
}
}
else
{
lean_dec(x_278);
lean_dec(x_271);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_290;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_278);
lean_dec(x_271);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_390 = lean_ctor_get(x_287, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_287, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_392 = x_287;
} else {
 lean_dec_ref(x_287);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_391);
return x_393;
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_13);
x_15 = lean_infer_type(x_13, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_18 = l_Lean_Meta_isClass_x3f(x_16, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_26 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__2;
x_27 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Name_isMetaprogramming_spec__0(x_19, x_26);
lean_dec(x_19);
if (x_27 == 0)
{
lean_dec(x_13);
x_21 = x_4;
goto block_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = l_Lean_Elab_Tactic_refineCore___lam__1___closed__5;
x_29 = l_Lean_MessageData_ofConst(x_13);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_array_push(x_4, x_31);
x_21 = x_32;
goto block_25;
}
block_25:
{
size_t x_22; size_t x_23; 
x_22 = 1;
x_23 = lean_usize_add(x_2, x_22);
x_2 = x_23;
x_4 = x_21;
x_9 = x_20;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
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
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_41 = !lean_is_exclusive(x_12);
if (x_41 == 0)
{
return x_12;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_12, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_12);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_9);
return x_45;
}
}
}
static lean_object* _init_l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___closed__0;
x_10 = lean_nat_dec_lt(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_le(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_usize_of_nat(x_2);
x_16 = lean_usize_of_nat(x_3);
x_17 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(x_1, x_15, x_16, x_9, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
}
}
}
static lean_object* _init_l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_lt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg___closed__0;
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__2;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_207; uint8_t x_232; 
x_146 = lean_st_ref_get(x_7, x_8);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_149 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_6, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_6, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_6, 5);
lean_inc(x_153);
x_154 = lean_ctor_get(x_6, 6);
lean_inc(x_154);
x_155 = lean_ctor_get(x_6, 7);
lean_inc(x_155);
x_156 = lean_ctor_get(x_6, 8);
lean_inc(x_156);
x_157 = lean_ctor_get(x_6, 9);
lean_inc(x_157);
x_158 = lean_ctor_get(x_6, 10);
lean_inc(x_158);
x_159 = lean_ctor_get(x_6, 11);
lean_inc(x_159);
x_160 = lean_ctor_get_uint8(x_6, sizeof(void*)*13 + 1);
x_161 = lean_ctor_get(x_6, 12);
lean_inc_ref(x_161);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 lean_ctor_release(x_6, 10);
 lean_ctor_release(x_6, 11);
 lean_ctor_release(x_6, 12);
 x_162 = x_6;
} else {
 lean_dec_ref(x_6);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_163);
lean_dec(x_147);
x_164 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__24;
x_165 = 1;
x_166 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_151, x_164, x_165);
x_167 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_166, x_164);
x_232 = l_Lean_Kernel_isDiagnosticsEnabled(x_163);
lean_dec_ref(x_163);
if (x_232 == 0)
{
if (x_167 == 0)
{
x_168 = x_149;
x_169 = x_150;
x_170 = x_152;
x_171 = x_153;
x_172 = x_154;
x_173 = x_155;
x_174 = x_156;
x_175 = x_157;
x_176 = x_158;
x_177 = x_159;
x_178 = x_160;
x_179 = x_161;
x_180 = x_7;
x_181 = x_148;
goto block_206;
}
else
{
x_207 = x_232;
goto block_231;
}
}
else
{
x_207 = x_167;
goto block_231;
}
block_28:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_get_size(x_14);
x_16 = l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(x_14, x_13, x_15, x_4, x_5, x_9, x_12, x_11);
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_10);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
block_38:
{
lean_object* x_37; 
x_37 = l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg(x_34, x_29, x_36);
lean_dec(x_36);
x_9 = x_30;
x_10 = x_31;
x_11 = x_32;
x_12 = x_33;
x_13 = x_35;
x_14 = x_37;
goto block_28;
}
block_48:
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_46, x_40);
if (x_47 == 0)
{
lean_dec(x_40);
lean_inc(x_46);
x_29 = x_46;
x_30 = x_39;
x_31 = x_41;
x_32 = x_42;
x_33 = x_44;
x_34 = x_43;
x_35 = x_45;
x_36 = x_46;
goto block_38;
}
else
{
x_29 = x_46;
x_30 = x_39;
x_31 = x_41;
x_32 = x_42;
x_33 = x_44;
x_34 = x_43;
x_35 = x_45;
x_36 = x_40;
goto block_38;
}
}
block_138:
{
lean_object* x_53; uint64_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_53 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_56 = lean_ctor_get(x_4, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_4, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 5);
lean_inc(x_60);
x_61 = lean_ctor_get(x_4, 6);
lean_inc(x_61);
x_62 = !lean_is_exclusive(x_53);
if (x_62 == 0)
{
uint8_t x_63; uint8_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_64 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_ctor_set_uint8(x_53, 9, x_52);
x_65 = 2;
x_66 = lean_uint64_shift_right(x_54, x_65);
x_67 = lean_uint64_shift_left(x_66, x_65);
x_68 = l_Lean_Meta_TransparencyMode_toUInt64(x_52);
x_69 = lean_uint64_lor(x_67, x_68);
x_70 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_56);
lean_ctor_set(x_70, 2, x_57);
lean_ctor_set(x_70, 3, x_58);
lean_ctor_set(x_70, 4, x_59);
lean_ctor_set(x_70, 5, x_60);
lean_ctor_set(x_70, 6, x_61);
lean_ctor_set_uint64(x_70, sizeof(void*)*7, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*7 + 8, x_55);
lean_ctor_set_uint8(x_70, sizeof(void*)*7 + 9, x_63);
lean_ctor_set_uint8(x_70, sizeof(void*)*7 + 10, x_64);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_5);
x_71 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_1, x_70, x_5, x_49, x_50, x_51);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_st_ref_get(x_5, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 4);
lean_inc_ref(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec_ref(x_74);
x_78 = lean_ctor_get(x_76, 0);
lean_inc_ref(x_78);
lean_dec_ref(x_76);
x_79 = lean_unsigned_to_nat(0u);
x_80 = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
x_81 = l_Lean_PersistentHashMap_foldl___at___Lean_mkModuleData_spec__4___redArg(x_78, x_2, x_80);
lean_dec_ref(x_78);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_eq(x_82, x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_sub(x_82, x_84);
lean_dec(x_82);
x_86 = lean_nat_dec_le(x_79, x_85);
if (x_86 == 0)
{
lean_inc(x_85);
x_39 = x_49;
x_40 = x_85;
x_41 = x_72;
x_42 = x_77;
x_43 = x_81;
x_44 = x_50;
x_45 = x_79;
x_46 = x_85;
goto block_48;
}
else
{
x_39 = x_49;
x_40 = x_85;
x_41 = x_72;
x_42 = x_77;
x_43 = x_81;
x_44 = x_50;
x_45 = x_79;
x_46 = x_79;
goto block_48;
}
}
else
{
lean_dec(x_82);
x_9 = x_49;
x_10 = x_72;
x_11 = x_77;
x_12 = x_50;
x_13 = x_79;
x_14 = x_81;
goto block_28;
}
}
else
{
uint8_t x_87; 
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_71);
if (x_87 == 0)
{
return x_71;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_71, 0);
x_89 = lean_ctor_get(x_71, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_71);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; lean_object* x_117; lean_object* x_118; 
x_91 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_92 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_93 = lean_ctor_get_uint8(x_53, 0);
x_94 = lean_ctor_get_uint8(x_53, 1);
x_95 = lean_ctor_get_uint8(x_53, 2);
x_96 = lean_ctor_get_uint8(x_53, 3);
x_97 = lean_ctor_get_uint8(x_53, 4);
x_98 = lean_ctor_get_uint8(x_53, 5);
x_99 = lean_ctor_get_uint8(x_53, 6);
x_100 = lean_ctor_get_uint8(x_53, 7);
x_101 = lean_ctor_get_uint8(x_53, 8);
x_102 = lean_ctor_get_uint8(x_53, 10);
x_103 = lean_ctor_get_uint8(x_53, 11);
x_104 = lean_ctor_get_uint8(x_53, 12);
x_105 = lean_ctor_get_uint8(x_53, 13);
x_106 = lean_ctor_get_uint8(x_53, 14);
x_107 = lean_ctor_get_uint8(x_53, 15);
x_108 = lean_ctor_get_uint8(x_53, 16);
x_109 = lean_ctor_get_uint8(x_53, 17);
x_110 = lean_ctor_get_uint8(x_53, 18);
lean_dec(x_53);
x_111 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_111, 0, x_93);
lean_ctor_set_uint8(x_111, 1, x_94);
lean_ctor_set_uint8(x_111, 2, x_95);
lean_ctor_set_uint8(x_111, 3, x_96);
lean_ctor_set_uint8(x_111, 4, x_97);
lean_ctor_set_uint8(x_111, 5, x_98);
lean_ctor_set_uint8(x_111, 6, x_99);
lean_ctor_set_uint8(x_111, 7, x_100);
lean_ctor_set_uint8(x_111, 8, x_101);
lean_ctor_set_uint8(x_111, 9, x_52);
lean_ctor_set_uint8(x_111, 10, x_102);
lean_ctor_set_uint8(x_111, 11, x_103);
lean_ctor_set_uint8(x_111, 12, x_104);
lean_ctor_set_uint8(x_111, 13, x_105);
lean_ctor_set_uint8(x_111, 14, x_106);
lean_ctor_set_uint8(x_111, 15, x_107);
lean_ctor_set_uint8(x_111, 16, x_108);
lean_ctor_set_uint8(x_111, 17, x_109);
lean_ctor_set_uint8(x_111, 18, x_110);
x_112 = 2;
x_113 = lean_uint64_shift_right(x_54, x_112);
x_114 = lean_uint64_shift_left(x_113, x_112);
x_115 = l_Lean_Meta_TransparencyMode_toUInt64(x_52);
x_116 = lean_uint64_lor(x_114, x_115);
x_117 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_117, 0, x_111);
lean_ctor_set(x_117, 1, x_56);
lean_ctor_set(x_117, 2, x_57);
lean_ctor_set(x_117, 3, x_58);
lean_ctor_set(x_117, 4, x_59);
lean_ctor_set(x_117, 5, x_60);
lean_ctor_set(x_117, 6, x_61);
lean_ctor_set_uint64(x_117, sizeof(void*)*7, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*7 + 8, x_55);
lean_ctor_set_uint8(x_117, sizeof(void*)*7 + 9, x_91);
lean_ctor_set_uint8(x_117, sizeof(void*)*7 + 10, x_92);
lean_inc(x_50);
lean_inc_ref(x_49);
lean_inc(x_5);
x_118 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_1, x_117, x_5, x_49, x_50, x_51);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec_ref(x_118);
x_121 = lean_st_ref_get(x_5, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 4);
lean_inc_ref(x_123);
lean_dec(x_122);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec_ref(x_121);
x_125 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_125);
lean_dec_ref(x_123);
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
x_128 = l_Lean_PersistentHashMap_foldl___at___Lean_mkModuleData_spec__4___redArg(x_125, x_2, x_127);
lean_dec_ref(x_125);
x_129 = lean_array_get_size(x_128);
x_130 = lean_nat_dec_eq(x_129, x_126);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_sub(x_129, x_131);
lean_dec(x_129);
x_133 = lean_nat_dec_le(x_126, x_132);
if (x_133 == 0)
{
lean_inc(x_132);
x_39 = x_49;
x_40 = x_132;
x_41 = x_119;
x_42 = x_124;
x_43 = x_128;
x_44 = x_50;
x_45 = x_126;
x_46 = x_132;
goto block_48;
}
else
{
x_39 = x_49;
x_40 = x_132;
x_41 = x_119;
x_42 = x_124;
x_43 = x_128;
x_44 = x_50;
x_45 = x_126;
x_46 = x_126;
goto block_48;
}
}
else
{
lean_dec(x_129);
x_9 = x_49;
x_10 = x_119;
x_11 = x_124;
x_12 = x_50;
x_13 = x_126;
x_14 = x_128;
goto block_28;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_134 = lean_ctor_get(x_118, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_118, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_136 = x_118;
} else {
 lean_dec_ref(x_118);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
block_145:
{
lean_object* x_142; uint8_t x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_142);
x_143 = lean_ctor_get_uint8(x_142, 9);
lean_dec_ref(x_142);
x_144 = l_Lean_Meta_TransparencyMode_lt(x_143, x_3);
if (x_144 == 0)
{
x_49 = x_139;
x_50 = x_140;
x_51 = x_141;
x_52 = x_143;
goto block_138;
}
else
{
x_49 = x_139;
x_50 = x_140;
x_51 = x_141;
x_52 = x_3;
goto block_138;
}
}
block_206:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_182 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__25;
x_183 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_166, x_182);
if (lean_is_scalar(x_162)) {
 x_184 = lean_alloc_ctor(0, 13, 2);
} else {
 x_184 = x_162;
}
lean_ctor_set(x_184, 0, x_168);
lean_ctor_set(x_184, 1, x_169);
lean_ctor_set(x_184, 2, x_166);
lean_ctor_set(x_184, 3, x_170);
lean_ctor_set(x_184, 4, x_183);
lean_ctor_set(x_184, 5, x_171);
lean_ctor_set(x_184, 6, x_172);
lean_ctor_set(x_184, 7, x_173);
lean_ctor_set(x_184, 8, x_174);
lean_ctor_set(x_184, 9, x_175);
lean_ctor_set(x_184, 10, x_176);
lean_ctor_set(x_184, 11, x_177);
lean_ctor_set(x_184, 12, x_179);
lean_ctor_set_uint8(x_184, sizeof(void*)*13, x_167);
lean_ctor_set_uint8(x_184, sizeof(void*)*13 + 1, x_178);
x_185 = l_Lean_isDiagnosticsEnabled___redArg(x_184, x_181);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_unbox(x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec_ref(x_185);
x_139 = x_184;
x_140 = x_180;
x_141 = x_188;
goto block_145;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_dec_ref(x_185);
x_190 = lean_st_ref_take(x_5, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec_ref(x_190);
x_193 = !lean_is_exclusive(x_191);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_191, 4);
lean_dec(x_194);
x_195 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__3;
lean_ctor_set(x_191, 4, x_195);
x_196 = lean_st_ref_set(x_5, x_191, x_192);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec_ref(x_196);
x_139 = x_184;
x_140 = x_180;
x_141 = x_197;
goto block_145;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_198 = lean_ctor_get(x_191, 0);
x_199 = lean_ctor_get(x_191, 1);
x_200 = lean_ctor_get(x_191, 2);
x_201 = lean_ctor_get(x_191, 3);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_191);
x_202 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__3;
x_203 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_199);
lean_ctor_set(x_203, 2, x_200);
lean_ctor_set(x_203, 3, x_201);
lean_ctor_set(x_203, 4, x_202);
x_204 = lean_st_ref_set(x_5, x_203, x_192);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec_ref(x_204);
x_139 = x_184;
x_140 = x_180;
x_141 = x_205;
goto block_145;
}
}
}
block_231:
{
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = lean_st_ref_take(x_7, x_148);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec_ref(x_208);
x_211 = !lean_is_exclusive(x_209);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_209, 0);
x_213 = lean_ctor_get(x_209, 5);
lean_dec(x_213);
x_214 = l_Lean_Kernel_enableDiag(x_212, x_167);
x_215 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28;
lean_ctor_set(x_209, 5, x_215);
lean_ctor_set(x_209, 0, x_214);
x_216 = lean_st_ref_set(x_7, x_209, x_210);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec_ref(x_216);
x_168 = x_149;
x_169 = x_150;
x_170 = x_152;
x_171 = x_153;
x_172 = x_154;
x_173 = x_155;
x_174 = x_156;
x_175 = x_157;
x_176 = x_158;
x_177 = x_159;
x_178 = x_160;
x_179 = x_161;
x_180 = x_7;
x_181 = x_217;
goto block_206;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_218 = lean_ctor_get(x_209, 0);
x_219 = lean_ctor_get(x_209, 1);
x_220 = lean_ctor_get(x_209, 2);
x_221 = lean_ctor_get(x_209, 3);
x_222 = lean_ctor_get(x_209, 4);
x_223 = lean_ctor_get(x_209, 6);
x_224 = lean_ctor_get(x_209, 7);
x_225 = lean_ctor_get(x_209, 8);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_209);
x_226 = l_Lean_Kernel_enableDiag(x_218, x_167);
x_227 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28;
x_228 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_219);
lean_ctor_set(x_228, 2, x_220);
lean_ctor_set(x_228, 3, x_221);
lean_ctor_set(x_228, 4, x_222);
lean_ctor_set(x_228, 5, x_227);
lean_ctor_set(x_228, 6, x_223);
lean_ctor_set(x_228, 7, x_224);
lean_ctor_set(x_228, 8, x_225);
x_229 = lean_st_ref_set(x_7, x_228, x_210);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec_ref(x_229);
x_168 = x_149;
x_169 = x_150;
x_170 = x_152;
x_171 = x_153;
x_172 = x_154;
x_173 = x_155;
x_174 = x_156;
x_175 = x_157;
x_176 = x_158;
x_177 = x_159;
x_178 = x_160;
x_179 = x_161;
x_180 = x_7;
x_181 = x_230;
goto block_206;
}
}
else
{
x_168 = x_149;
x_169 = x_150;
x_170 = x_152;
x_171 = x_153;
x_172 = x_154;
x_173 = x_155;
x_174 = x_156;
x_175 = x_157;
x_176 = x_158;
x_177 = x_159;
x_178 = x_160;
x_179 = x_161;
x_180 = x_7;
x_181 = x_148;
goto block_206;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' failed for proposition", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nsince its '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instance", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ndid not reduce to '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' or '", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'.\n\n", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Classical", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("choice", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__15;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Reduction got stuck on '", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', which indicates that a '", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instance is defined using classical reasoning, proving an instance exists rather than giving a concrete construction. The '", 125, 125);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' tactic works by evaluating a decision procedure via reduction, and it cannot make progress with such instances. This can occur due to the 'opened scoped Classical' command, which enables the instance '", 203, 203);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__23;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("propDecidable", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__25;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'.", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__27;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Reduction got stuck on '▸' (", 30, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__29;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("), which suggests that one of the '", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__31;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instances is defined using tactics such as 'rw' or 'simp'. To avoid tactics, make use of functions such as '", 110, 110);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__33;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inferInstanceAs", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__35;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decidable_of_decidable_of_iff", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__37;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to alter a proposition.", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__39;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("After unfolding the ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__41;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__43;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", reduction got stuck at the '", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__45;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instances", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instance", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Reduction got stuck at the '", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__49;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' proved that the proposition", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__51;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__53() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' failed. internal error: the elaborator is able to reduce the '", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__53;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__55() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__1;
x_3 = l_Lean_MessageData_ofConstName(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__56() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instance, but the kernel is not able to", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__56;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_134; lean_object* x_135; 
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_205; uint64_t x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; lean_object* x_235; uint8_t x_236; uint8_t x_252; 
x_205 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_205);
x_206 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_207 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_208 = lean_ctor_get(x_7, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_210);
x_211 = lean_ctor_get(x_7, 4);
lean_inc(x_211);
x_212 = lean_ctor_get(x_7, 5);
lean_inc(x_212);
x_213 = lean_ctor_get(x_7, 6);
lean_inc(x_213);
x_214 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_215 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
x_216 = lean_ctor_get_uint8(x_205, 0);
x_217 = lean_ctor_get_uint8(x_205, 1);
x_218 = lean_ctor_get_uint8(x_205, 2);
x_219 = lean_ctor_get_uint8(x_205, 3);
x_220 = lean_ctor_get_uint8(x_205, 4);
x_221 = lean_ctor_get_uint8(x_205, 5);
x_222 = lean_ctor_get_uint8(x_205, 6);
x_223 = lean_ctor_get_uint8(x_205, 7);
x_224 = lean_ctor_get_uint8(x_205, 8);
x_225 = lean_ctor_get_uint8(x_205, 9);
x_226 = lean_ctor_get_uint8(x_205, 10);
x_227 = lean_ctor_get_uint8(x_205, 11);
x_228 = lean_ctor_get_uint8(x_205, 12);
x_229 = lean_ctor_get_uint8(x_205, 13);
x_230 = lean_ctor_get_uint8(x_205, 14);
x_231 = lean_ctor_get_uint8(x_205, 15);
x_232 = lean_ctor_get_uint8(x_205, 16);
x_233 = lean_ctor_get_uint8(x_205, 17);
x_234 = lean_ctor_get_uint8(x_205, 18);
if (lean_is_exclusive(x_205)) {
 x_235 = x_205;
} else {
 lean_dec_ref(x_205);
 x_235 = lean_box(0);
}
x_252 = l_Lean_Meta_TransparencyMode_lt(x_225, x_6);
if (x_252 == 0)
{
x_236 = x_225;
goto block_251;
}
else
{
x_236 = x_6;
goto block_251;
}
block_251:
{
lean_object* x_237; uint64_t x_238; uint64_t x_239; uint64_t x_240; uint64_t x_241; uint64_t x_242; lean_object* x_243; lean_object* x_244; 
if (lean_is_scalar(x_235)) {
 x_237 = lean_alloc_ctor(0, 0, 19);
} else {
 x_237 = x_235;
}
lean_ctor_set_uint8(x_237, 0, x_216);
lean_ctor_set_uint8(x_237, 1, x_217);
lean_ctor_set_uint8(x_237, 2, x_218);
lean_ctor_set_uint8(x_237, 3, x_219);
lean_ctor_set_uint8(x_237, 4, x_220);
lean_ctor_set_uint8(x_237, 5, x_221);
lean_ctor_set_uint8(x_237, 6, x_222);
lean_ctor_set_uint8(x_237, 7, x_223);
lean_ctor_set_uint8(x_237, 8, x_224);
lean_ctor_set_uint8(x_237, 9, x_236);
lean_ctor_set_uint8(x_237, 10, x_226);
lean_ctor_set_uint8(x_237, 11, x_227);
lean_ctor_set_uint8(x_237, 12, x_228);
lean_ctor_set_uint8(x_237, 13, x_229);
lean_ctor_set_uint8(x_237, 14, x_230);
lean_ctor_set_uint8(x_237, 15, x_231);
lean_ctor_set_uint8(x_237, 16, x_232);
lean_ctor_set_uint8(x_237, 17, x_233);
lean_ctor_set_uint8(x_237, 18, x_234);
x_238 = 2;
x_239 = lean_uint64_shift_right(x_206, x_238);
x_240 = lean_uint64_shift_left(x_239, x_238);
x_241 = l_Lean_Meta_TransparencyMode_toUInt64(x_236);
x_242 = lean_uint64_lor(x_240, x_241);
x_243 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_243, 0, x_237);
lean_ctor_set(x_243, 1, x_208);
lean_ctor_set(x_243, 2, x_209);
lean_ctor_set(x_243, 3, x_210);
lean_ctor_set(x_243, 4, x_211);
lean_ctor_set(x_243, 5, x_212);
lean_ctor_set(x_243, 6, x_213);
lean_ctor_set_uint64(x_243, sizeof(void*)*7, x_242);
lean_ctor_set_uint8(x_243, sizeof(void*)*7 + 8, x_207);
lean_ctor_set_uint8(x_243, sizeof(void*)*7 + 9, x_214);
lean_ctor_set_uint8(x_243, sizeof(void*)*7 + 10, x_215);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_3);
x_244 = lean_whnf(x_3, x_243, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec_ref(x_244);
x_134 = x_245;
x_135 = x_246;
goto block_204;
}
else
{
uint8_t x_247; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_244);
if (x_247 == 0)
{
return x_244;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_244, 0);
x_249 = lean_ctor_get(x_244, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_244);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
}
else
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_5, 0);
lean_inc(x_253);
lean_dec(x_5);
x_134 = x_253;
x_135 = x_11;
goto block_204;
}
block_51:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_19 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1;
x_20 = l_Lean_MessageData_ofName(x_1);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__1;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_indentExpr(x_2);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__3;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Name_mkStr1(x_15);
x_29 = l_Lean_MessageData_ofConstName(x_28, x_17);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__5;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_indentExpr(x_3);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__7;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_MessageData_ofConstName(x_14, x_17);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__9;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_MessageData_ofConstName(x_13, x_17);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__11;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_12);
x_46 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_18);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_16);
return x_50;
}
block_105:
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__13;
x_60 = l_Lean_Expr_isAppOf(x_52, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__16;
x_62 = l_Lean_Expr_isAppOf(x_52, x_61);
lean_dec_ref(x_52);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = l_Lean_MessageData_nil;
x_12 = x_58;
x_13 = x_53;
x_14 = x_55;
x_15 = x_54;
x_16 = x_56;
x_17 = x_57;
x_18 = x_63;
goto block_51;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_64 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__18;
x_65 = l_Lean_MessageData_ofConstName(x_61, x_57);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__20;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_inc_ref(x_54);
x_69 = l_Lean_Name_mkStr1(x_54);
x_70 = l_Lean_MessageData_ofConstName(x_69, x_57);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__22;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_1);
x_74 = l_Lean_MessageData_ofName(x_1);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__24;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__26;
x_79 = l_Lean_MessageData_ofConstName(x_78, x_57);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__28;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_MessageData_hint_x27(x_82);
x_12 = x_58;
x_13 = x_53;
x_14 = x_55;
x_15 = x_54;
x_16 = x_56;
x_17 = x_57;
x_18 = x_83;
goto block_51;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_52);
x_84 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__30;
x_85 = l_Lean_MessageData_ofConstName(x_59, x_57);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__32;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_inc_ref(x_54);
x_89 = l_Lean_Name_mkStr1(x_54);
x_90 = l_Lean_MessageData_ofConstName(x_89, x_57);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__34;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__36;
x_95 = l_Lean_MessageData_ofConstName(x_94, x_57);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__9;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__38;
x_100 = l_Lean_MessageData_ofConstName(x_99, x_57);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__40;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_MessageData_hint_x27(x_103);
x_12 = x_58;
x_13 = x_53;
x_14 = x_55;
x_15 = x_54;
x_16 = x_56;
x_17 = x_57;
x_18 = x_104;
goto block_51;
}
}
block_133:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_114 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__42;
x_115 = l_Lean_stringToMessageData(x_113);
lean_dec_ref(x_113);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__44;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_array_to_list(x_110);
x_120 = l_Lean_MessageData_andList(x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__46;
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_inc_ref(x_109);
x_124 = l_Lean_Name_mkStr1(x_109);
x_125 = l_Lean_MessageData_ofConstName(x_124, x_112);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__5;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_inc_ref(x_106);
x_129 = l_Lean_indentExpr(x_106);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_52 = x_106;
x_53 = x_107;
x_54 = x_109;
x_55 = x_108;
x_56 = x_111;
x_57 = x_112;
x_58 = x_132;
goto block_105;
}
block_204:
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__0;
x_137 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__4;
x_138 = l_Lean_Expr_isAppOf(x_134, x_137);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__6;
x_140 = l_Lean_Expr_isAppOf(x_134, x_139);
lean_dec_ref(x_134);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = l_Lean_withoutModifyingState___at___Lean_Meta_addPPExplicitToExposeDiff_spec__0___redArg(x_4, x_7, x_8, x_9, x_10, x_135);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec_ref(x_141);
x_144 = !lean_is_exclusive(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_ctor_get(x_142, 0);
x_146 = lean_ctor_get(x_142, 1);
x_147 = l_Array_isEmpty___redArg(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
lean_free_object(x_142);
x_148 = lean_array_get_size(x_146);
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_dec_eq(x_148, x_149);
lean_dec(x_148);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__47;
x_106 = x_145;
x_107 = x_139;
x_108 = x_137;
x_109 = x_136;
x_110 = x_146;
x_111 = x_143;
x_112 = x_140;
x_113 = x_151;
goto block_133;
}
else
{
lean_object* x_152; 
x_152 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__48;
x_106 = x_145;
x_107 = x_139;
x_108 = x_137;
x_109 = x_136;
x_110 = x_146;
x_111 = x_143;
x_112 = x_140;
x_113 = x_152;
goto block_133;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_146);
x_153 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__50;
x_154 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__1;
x_155 = l_Lean_MessageData_ofConstName(x_154, x_140);
lean_ctor_set_tag(x_142, 7);
lean_ctor_set(x_142, 1, x_155);
lean_ctor_set(x_142, 0, x_153);
x_156 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__5;
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_142);
lean_ctor_set(x_157, 1, x_156);
lean_inc(x_145);
x_158 = l_Lean_indentExpr(x_145);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_52 = x_145;
x_53 = x_139;
x_54 = x_136;
x_55 = x_137;
x_56 = x_143;
x_57 = x_140;
x_58 = x_161;
goto block_105;
}
}
else
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_162 = lean_ctor_get(x_142, 0);
x_163 = lean_ctor_get(x_142, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_142);
x_164 = l_Array_isEmpty___redArg(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_165 = lean_array_get_size(x_163);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_dec_eq(x_165, x_166);
lean_dec(x_165);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__47;
x_106 = x_162;
x_107 = x_139;
x_108 = x_137;
x_109 = x_136;
x_110 = x_163;
x_111 = x_143;
x_112 = x_140;
x_113 = x_168;
goto block_133;
}
else
{
lean_object* x_169; 
x_169 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__48;
x_106 = x_162;
x_107 = x_139;
x_108 = x_137;
x_109 = x_136;
x_110 = x_163;
x_111 = x_143;
x_112 = x_140;
x_113 = x_169;
goto block_133;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_163);
x_170 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__50;
x_171 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__1;
x_172 = l_Lean_MessageData_ofConstName(x_171, x_140);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__5;
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
lean_inc(x_162);
x_176 = l_Lean_indentExpr(x_162);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_52 = x_162;
x_53 = x_139;
x_54 = x_136;
x_55 = x_137;
x_56 = x_143;
x_57 = x_140;
x_58 = x_179;
goto block_105;
}
}
}
else
{
uint8_t x_180; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_141);
if (x_180 == 0)
{
return x_141;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_141, 0);
x_182 = lean_ctor_get(x_141, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_141);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
x_184 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1;
x_185 = l_Lean_MessageData_ofName(x_1);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__52;
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_indentExpr(x_2);
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__5;
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_135);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec_ref(x_134);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_194 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1;
x_195 = l_Lean_MessageData_ofName(x_1);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__54;
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__55;
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__57;
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_135);
return x_203;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__0___boxed), 3, 0);
x_11 = 1;
x_12 = lean_box(x_11);
lean_inc_ref(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___boxed), 8, 3);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_12);
x_14 = lean_box(x_11);
lean_inc_ref(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___boxed), 11, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_14);
x_16 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__16;
x_17 = lean_array_push(x_16, x_2);
x_18 = l_Lean_MessageData_ofLazyM(x_15, x_17);
x_19 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_18, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg(x_1, x_3, x_4, x_5, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
x_13 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalDecideCore_diagnose(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doElab___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
x_8 = l_Lean_Meta_mkDecideProof(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_68; uint8_t x_69; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_3, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 6);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_22 = lean_ctor_get_uint8(x_9, 0);
x_23 = lean_ctor_get_uint8(x_9, 1);
x_24 = lean_ctor_get_uint8(x_9, 2);
x_25 = lean_ctor_get_uint8(x_9, 3);
x_26 = lean_ctor_get_uint8(x_9, 4);
x_27 = lean_ctor_get_uint8(x_9, 5);
x_28 = lean_ctor_get_uint8(x_9, 6);
x_29 = lean_ctor_get_uint8(x_9, 7);
x_30 = lean_ctor_get_uint8(x_9, 8);
x_31 = lean_ctor_get_uint8(x_9, 9);
x_32 = lean_ctor_get_uint8(x_9, 10);
x_33 = lean_ctor_get_uint8(x_9, 11);
x_34 = lean_ctor_get_uint8(x_9, 12);
x_35 = lean_ctor_get_uint8(x_9, 13);
x_36 = lean_ctor_get_uint8(x_9, 14);
x_37 = lean_ctor_get_uint8(x_9, 15);
x_38 = lean_ctor_get_uint8(x_9, 16);
x_39 = lean_ctor_get_uint8(x_9, 17);
x_40 = lean_ctor_get_uint8(x_9, 18);
if (lean_is_exclusive(x_9)) {
 x_41 = x_9;
} else {
 lean_dec_ref(x_9);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Expr_appFn_x21(x_10);
x_43 = l_Lean_Expr_appArg_x21(x_42);
lean_dec_ref(x_42);
x_68 = 1;
x_69 = l_Lean_Meta_TransparencyMode_lt(x_31, x_68);
if (x_69 == 0)
{
x_44 = x_31;
goto block_67;
}
else
{
x_44 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; lean_object* x_51; lean_object* x_52; 
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 0, 19);
} else {
 x_45 = x_41;
}
lean_ctor_set_uint8(x_45, 0, x_22);
lean_ctor_set_uint8(x_45, 1, x_23);
lean_ctor_set_uint8(x_45, 2, x_24);
lean_ctor_set_uint8(x_45, 3, x_25);
lean_ctor_set_uint8(x_45, 4, x_26);
lean_ctor_set_uint8(x_45, 5, x_27);
lean_ctor_set_uint8(x_45, 6, x_28);
lean_ctor_set_uint8(x_45, 7, x_29);
lean_ctor_set_uint8(x_45, 8, x_30);
lean_ctor_set_uint8(x_45, 9, x_44);
lean_ctor_set_uint8(x_45, 10, x_32);
lean_ctor_set_uint8(x_45, 11, x_33);
lean_ctor_set_uint8(x_45, 12, x_34);
lean_ctor_set_uint8(x_45, 13, x_35);
lean_ctor_set_uint8(x_45, 14, x_36);
lean_ctor_set_uint8(x_45, 15, x_37);
lean_ctor_set_uint8(x_45, 16, x_38);
lean_ctor_set_uint8(x_45, 17, x_39);
lean_ctor_set_uint8(x_45, 18, x_40);
x_46 = 2;
x_47 = lean_uint64_shift_right(x_12, x_46);
x_48 = lean_uint64_shift_left(x_47, x_46);
x_49 = l_Lean_Meta_TransparencyMode_toUInt64(x_44);
x_50 = lean_uint64_lor(x_48, x_49);
x_51 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_14);
lean_ctor_set(x_51, 2, x_15);
lean_ctor_set(x_51, 3, x_16);
lean_ctor_set(x_51, 4, x_17);
lean_ctor_set(x_51, 5, x_18);
lean_ctor_set(x_51, 6, x_19);
lean_ctor_set_uint64(x_51, sizeof(void*)*7, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 8, x_13);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 9, x_20);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 10, x_21);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_43);
x_52 = lean_whnf(x_43, x_51, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__4;
x_57 = l_Lean_Expr_isAppOf(x_54, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_free_object(x_52);
lean_dec(x_10);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_54);
x_59 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg(x_1, x_2, x_43, x_58, x_3, x_4, x_5, x_6, x_55);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_59;
}
else
{
lean_dec(x_54);
lean_dec_ref(x_43);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
lean_ctor_set(x_52, 0, x_10);
return x_52;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
x_62 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__4;
x_63 = l_Lean_Expr_isAppOf(x_60, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_10);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_60);
x_65 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg(x_1, x_2, x_43, x_64, x_3, x_4, x_5, x_6, x_61);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_65;
}
else
{
lean_object* x_66; 
lean_dec(x_60);
lean_dec_ref(x_43);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_10);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
}
else
{
lean_dec_ref(x_43);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_52;
}
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalDecideCore_doElab___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalDecideCore_doElab(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_1, x_6);
if (x_8 == 0)
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_1, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_3);
x_2 = x_12;
x_3 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_11 = l_Lean_Meta_mkDecideProof(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_96; uint8_t x_121; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_Elab_Term_getLevelNames___redArg(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_Elab_Tactic_saveState___redArg(x_3, x_5, x_7, x_9, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_st_ref_get(x_9, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__9;
lean_inc_ref(x_2);
x_25 = l_Lean_CollectLevelParams_main(x_2, x_24);
x_26 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_26);
lean_dec_ref(x_25);
x_27 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_8, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_8, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 6);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 7);
lean_inc(x_33);
x_34 = lean_ctor_get(x_8, 8);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 9);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 10);
lean_inc(x_36);
x_37 = lean_ctor_get(x_8, 11);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_39 = lean_ctor_get(x_8, 12);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_40);
lean_dec(x_21);
x_41 = l_Lean_Expr_appFn_x21(x_12);
x_42 = l_Lean_Expr_appArg_x21(x_41);
lean_dec_ref(x_41);
x_52 = l_List_reverse___redArg(x_15);
x_53 = lean_box(0);
x_54 = l_List_filterTR_loop___at___Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(x_26, x_52, x_53);
lean_dec_ref(x_26);
x_55 = lean_box(0);
x_56 = 1;
x_57 = 0;
x_58 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__23;
x_59 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_29, x_58, x_57);
x_60 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__24;
x_61 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_59, x_60);
x_121 = l_Lean_Kernel_isDiagnosticsEnabled(x_40);
lean_dec_ref(x_40);
if (x_121 == 0)
{
if (x_61 == 0)
{
lean_inc(x_9);
x_62 = x_27;
x_63 = x_28;
x_64 = x_30;
x_65 = x_31;
x_66 = x_32;
x_67 = x_33;
x_68 = x_34;
x_69 = x_35;
x_70 = x_36;
x_71 = x_37;
x_72 = x_38;
x_73 = x_39;
x_74 = x_9;
x_75 = x_22;
goto block_95;
}
else
{
x_96 = x_121;
goto block_120;
}
}
else
{
x_96 = x_61;
goto block_120;
}
block_51:
{
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_44);
lean_dec(x_23);
x_46 = l_Lean_Elab_Tactic_SavedState_restore___redArg(x_18, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg(x_1, x_2, x_42, x_48, x_6, x_7, x_8, x_9, x_47);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec_ref(x_42);
lean_dec(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_23)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_23;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_43);
return x_50;
}
}
block_95:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__25;
x_77 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_59, x_76);
x_78 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_78, 0, x_62);
lean_ctor_set(x_78, 1, x_63);
lean_ctor_set(x_78, 2, x_59);
lean_ctor_set(x_78, 3, x_64);
lean_ctor_set(x_78, 4, x_77);
lean_ctor_set(x_78, 5, x_65);
lean_ctor_set(x_78, 6, x_66);
lean_ctor_set(x_78, 7, x_67);
lean_ctor_set(x_78, 8, x_68);
lean_ctor_set(x_78, 9, x_69);
lean_ctor_set(x_78, 10, x_70);
lean_ctor_set(x_78, 11, x_71);
lean_ctor_set(x_78, 12, x_73);
lean_ctor_set_uint8(x_78, sizeof(void*)*13, x_61);
lean_ctor_set_uint8(x_78, sizeof(void*)*13 + 1, x_72);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
lean_inc(x_54);
x_79 = l_Lean_Meta_mkAuxLemma(x_54, x_2, x_12, x_55, x_56, x_57, x_6, x_7, x_78, x_74, x_75);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
lean_dec_ref(x_42);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_box(0);
x_83 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_54, x_82);
x_84 = l_Lean_Expr_const___override(x_81, x_83);
lean_ctor_set(x_79, 0, x_84);
return x_79;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_79);
x_87 = lean_box(0);
x_88 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_54, x_87);
x_89 = l_Lean_Expr_const___override(x_85, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_54);
x_91 = lean_ctor_get(x_79, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_79, 1);
lean_inc(x_92);
lean_dec_ref(x_79);
x_93 = l_Lean_Exception_isInterrupt(x_91);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Exception_isRuntime(x_91);
x_43 = x_92;
x_44 = x_91;
x_45 = x_94;
goto block_51;
}
else
{
x_43 = x_92;
x_44 = x_91;
x_45 = x_93;
goto block_51;
}
}
}
block_120:
{
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_st_ref_take(x_9, x_22);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_98, 0);
x_102 = lean_ctor_get(x_98, 5);
lean_dec(x_102);
x_103 = l_Lean_Kernel_enableDiag(x_101, x_61);
x_104 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28;
lean_ctor_set(x_98, 5, x_104);
lean_ctor_set(x_98, 0, x_103);
x_105 = lean_st_ref_set(x_9, x_98, x_99);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec_ref(x_105);
lean_inc(x_9);
x_62 = x_27;
x_63 = x_28;
x_64 = x_30;
x_65 = x_31;
x_66 = x_32;
x_67 = x_33;
x_68 = x_34;
x_69 = x_35;
x_70 = x_36;
x_71 = x_37;
x_72 = x_38;
x_73 = x_39;
x_74 = x_9;
x_75 = x_106;
goto block_95;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_107 = lean_ctor_get(x_98, 0);
x_108 = lean_ctor_get(x_98, 1);
x_109 = lean_ctor_get(x_98, 2);
x_110 = lean_ctor_get(x_98, 3);
x_111 = lean_ctor_get(x_98, 4);
x_112 = lean_ctor_get(x_98, 6);
x_113 = lean_ctor_get(x_98, 7);
x_114 = lean_ctor_get(x_98, 8);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_98);
x_115 = l_Lean_Kernel_enableDiag(x_107, x_61);
x_116 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28;
x_117 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_108);
lean_ctor_set(x_117, 2, x_109);
lean_ctor_set(x_117, 3, x_110);
lean_ctor_set(x_117, 4, x_111);
lean_ctor_set(x_117, 5, x_116);
lean_ctor_set(x_117, 6, x_112);
lean_ctor_set(x_117, 7, x_113);
lean_ctor_set(x_117, 8, x_114);
x_118 = lean_st_ref_set(x_9, x_117, x_99);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec_ref(x_118);
lean_inc(x_9);
x_62 = x_27;
x_63 = x_28;
x_64 = x_30;
x_65 = x_31;
x_66 = x_32;
x_67 = x_33;
x_68 = x_34;
x_69 = x_35;
x_70 = x_36;
x_71 = x_37;
x_72 = x_38;
x_73 = x_39;
x_74 = x_9;
x_75 = x_119;
goto block_95;
}
}
else
{
lean_inc(x_9);
x_62 = x_27;
x_63 = x_28;
x_64 = x_30;
x_65 = x_31;
x_66 = x_32;
x_67 = x_33;
x_68 = x_34;
x_69 = x_35;
x_70 = x_36;
x_71 = x_37;
x_72 = x_38;
x_73 = x_39;
x_74 = x_9;
x_75 = x_22;
goto block_95;
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterTR_loop___at___Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalDecideCore_doKernel(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' failed, cannot simultaneously set both '+kernel' and '+native'", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
if (x_2 == 0)
{
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = x_12;
x_21 = x_13;
x_22 = x_14;
goto block_33;
}
else
{
if (x_1 == 0)
{
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = x_12;
x_21 = x_13;
x_22 = x_14;
goto block_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec_ref(x_8);
lean_dec_ref(x_4);
x_34 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1;
x_35 = l_Lean_MessageData_ofName(x_3);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_38, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
block_33:
{
lean_object* x_23; 
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc_ref(x_16);
x_23 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide(x_4, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
if (x_1 == 0)
{
if (x_2 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Lean_Elab_Tactic_evalDecideCore_doElab___redArg(x_3, x_24, x_18, x_19, x_20, x_21, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec_ref(x_23);
x_29 = l_Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(x_3, x_27, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_28);
lean_dec_ref(x_16);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec_ref(x_23);
x_32 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg(x_3, x_30, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_31);
lean_dec_ref(x_16);
return x_32;
}
}
else
{
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec(x_3);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(x_12, x_14, x_1, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_16);
x_18 = l_Lean_MVarId_getDecl(x_16, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = l_Lean_LocalContext_getFVarIds(x_21);
lean_dec_ref(x_21);
x_23 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_24 = l_Lean_MVarId_revert(x_16, x_22, x_23, x_1, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_30);
lean_ctor_set(x_25, 0, x_28);
x_31 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_25, x_3, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_34, x_3, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 0);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_24);
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
lean_dec(x_16);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_ctor_get_uint8(x_2, 0);
x_13 = lean_ctor_get_uint8(x_2, 1);
x_14 = lean_ctor_get_uint8(x_2, 3);
x_15 = lean_box(x_13);
x_16 = lean_box(x_12);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed), 14, 3);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_1);
if (x_14 == 0)
{
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
goto block_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_box(x_14);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed), 10, 1);
lean_closure_set(x_31, 0, x_30);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_32 = l_Lean_Elab_Tactic_withMainContext___redArg(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_33;
goto block_29;
}
else
{
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_32;
}
}
block_29:
{
uint8_t x_27; lean_object* x_28; 
x_27 = 1;
x_28 = l_Lean_Elab_Tactic_closeMainGoalUsing(x_1, x_17, x_27, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_1);
x_16 = lean_unbox(x_2);
x_17 = l_Lean_Elab_Tactic_evalDecideCore___lam__0(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l_Lean_Elab_Tactic_evalDecideCore___lam__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalDecideCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("DecideConfig", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_;
x_8 = 0;
x_9 = l_Lean_Meta_evalExpr_x27___redArg(x_7, x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nException: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_;
x_2 = l_Lean_MessageData_ofName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6;
x_2 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_2 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__11() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 1;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, 1, x_2);
lean_ctor_set_uint8(x_3, 2, x_1);
lean_ctor_set_uint8(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_1);
x_34 = l_Lean_Parser_Tactic_getConfigItems(x_1);
x_35 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(x_34);
x_36 = l_Array_isEmpty___redArg(x_35);
x_37 = 1;
if (x_36 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_st_ref_get(x_8, x_9);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_7, 5);
x_43 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_43);
lean_dec(x_39);
x_44 = l_Lean_replaceRef(x_1, x_42);
lean_dec(x_42);
lean_dec(x_1);
lean_ctor_set(x_7, 5, x_44);
x_45 = l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_;
x_46 = l_Lean_Environment_contains(x_43, x_45, x_37);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec_ref(x_35);
x_47 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8;
x_48 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
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
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_53 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_33, x_45, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = l_Lean_Expr_hasSyntheticSorry(x_55);
if (x_57 == 0)
{
uint8_t x_58; 
lean_free_object(x_53);
x_58 = l_Lean_Expr_hasSorry(x_55);
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_55);
x_59 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_(x_55, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_dec(x_55);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = l_Lean_Exception_isInterrupt(x_60);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = l_Lean_Exception_isRuntime(x_60);
x_10 = x_60;
x_11 = x_61;
x_12 = x_6;
x_13 = x_8;
x_14 = x_5;
x_15 = x_4;
x_16 = x_55;
x_17 = x_7;
x_18 = x_3;
x_19 = x_59;
x_20 = x_63;
goto block_32;
}
else
{
x_10 = x_60;
x_11 = x_61;
x_12 = x_6;
x_13 = x_8;
x_14 = x_5;
x_15 = x_4;
x_16 = x_55;
x_17 = x_7;
x_18 = x_3;
x_19 = x_59;
x_20 = x_62;
goto block_32;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_55);
x_64 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10;
x_65 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
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
lean_dec(x_55);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_70 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_70, 0, x_36);
lean_ctor_set_uint8(x_70, 1, x_36);
lean_ctor_set_uint8(x_70, 2, x_57);
lean_ctor_set_uint8(x_70, 3, x_36);
lean_ctor_set(x_53, 0, x_70);
return x_53;
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_53, 0);
x_72 = lean_ctor_get(x_53, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_53);
x_73 = l_Lean_Expr_hasSyntheticSorry(x_71);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Expr_hasSorry(x_71);
if (x_74 == 0)
{
lean_object* x_75; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_71);
x_75 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_(x_71, x_5, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_dec(x_71);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
x_78 = l_Lean_Exception_isInterrupt(x_76);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Exception_isRuntime(x_76);
x_10 = x_76;
x_11 = x_77;
x_12 = x_6;
x_13 = x_8;
x_14 = x_5;
x_15 = x_4;
x_16 = x_71;
x_17 = x_7;
x_18 = x_3;
x_19 = x_75;
x_20 = x_79;
goto block_32;
}
else
{
x_10 = x_76;
x_11 = x_77;
x_12 = x_6;
x_13 = x_8;
x_14 = x_5;
x_15 = x_4;
x_16 = x_71;
x_17 = x_7;
x_18 = x_3;
x_19 = x_75;
x_20 = x_78;
goto block_32;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_71);
x_80 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10;
x_81 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_72);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
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
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_71);
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_86 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_86, 0, x_36);
lean_ctor_set_uint8(x_86, 1, x_36);
lean_ctor_set_uint8(x_86, 2, x_73);
lean_ctor_set_uint8(x_86, 3, x_36);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_72);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_88 = !lean_is_exclusive(x_53);
if (x_88 == 0)
{
return x_53;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_53, 0);
x_90 = lean_ctor_get(x_53, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_53);
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
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_92 = lean_ctor_get(x_7, 0);
x_93 = lean_ctor_get(x_7, 1);
x_94 = lean_ctor_get(x_7, 2);
x_95 = lean_ctor_get(x_7, 3);
x_96 = lean_ctor_get(x_7, 4);
x_97 = lean_ctor_get(x_7, 5);
x_98 = lean_ctor_get(x_7, 6);
x_99 = lean_ctor_get(x_7, 7);
x_100 = lean_ctor_get(x_7, 8);
x_101 = lean_ctor_get(x_7, 9);
x_102 = lean_ctor_get(x_7, 10);
x_103 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_104 = lean_ctor_get(x_7, 11);
x_105 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_106 = lean_ctor_get(x_7, 12);
lean_inc(x_106);
lean_inc(x_104);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_7);
x_107 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_107);
lean_dec(x_39);
x_108 = l_Lean_replaceRef(x_1, x_97);
lean_dec(x_97);
lean_dec(x_1);
x_109 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_109, 0, x_92);
lean_ctor_set(x_109, 1, x_93);
lean_ctor_set(x_109, 2, x_94);
lean_ctor_set(x_109, 3, x_95);
lean_ctor_set(x_109, 4, x_96);
lean_ctor_set(x_109, 5, x_108);
lean_ctor_set(x_109, 6, x_98);
lean_ctor_set(x_109, 7, x_99);
lean_ctor_set(x_109, 8, x_100);
lean_ctor_set(x_109, 9, x_101);
lean_ctor_set(x_109, 10, x_102);
lean_ctor_set(x_109, 11, x_104);
lean_ctor_set(x_109, 12, x_106);
lean_ctor_set_uint8(x_109, sizeof(void*)*13, x_103);
lean_ctor_set_uint8(x_109, sizeof(void*)*13 + 1, x_105);
x_110 = l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_;
x_111 = l_Lean_Environment_contains(x_107, x_110, x_37);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_35);
x_112 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8;
x_113 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_112, x_3, x_4, x_5, x_6, x_109, x_8, x_40);
lean_dec(x_8);
lean_dec_ref(x_109);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
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
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_object* x_118; 
lean_inc(x_8);
lean_inc_ref(x_109);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_118 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_33, x_110, x_35, x_3, x_4, x_5, x_6, x_109, x_8, x_40);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
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
x_122 = l_Lean_Expr_hasSyntheticSorry(x_119);
if (x_122 == 0)
{
uint8_t x_123; 
lean_dec(x_121);
x_123 = l_Lean_Expr_hasSorry(x_119);
if (x_123 == 0)
{
lean_object* x_124; 
lean_inc(x_8);
lean_inc_ref(x_109);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_119);
x_124 = l_Lean_Elab_Tactic_evalUnsafe___redArg____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_(x_119, x_5, x_6, x_109, x_8, x_120);
if (lean_obj_tag(x_124) == 0)
{
lean_dec(x_119);
lean_dec_ref(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
x_127 = l_Lean_Exception_isInterrupt(x_125);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = l_Lean_Exception_isRuntime(x_125);
x_10 = x_125;
x_11 = x_126;
x_12 = x_6;
x_13 = x_8;
x_14 = x_5;
x_15 = x_4;
x_16 = x_119;
x_17 = x_109;
x_18 = x_3;
x_19 = x_124;
x_20 = x_128;
goto block_32;
}
else
{
x_10 = x_125;
x_11 = x_126;
x_12 = x_6;
x_13 = x_8;
x_14 = x_5;
x_15 = x_4;
x_16 = x_119;
x_17 = x_109;
x_18 = x_3;
x_19 = x_124;
x_20 = x_127;
goto block_32;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_119);
x_129 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10;
x_130 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_129, x_3, x_4, x_5, x_6, x_109, x_8, x_120);
lean_dec(x_8);
lean_dec_ref(x_109);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_119);
lean_dec_ref(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_135 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_135, 0, x_36);
lean_ctor_set_uint8(x_135, 1, x_36);
lean_ctor_set_uint8(x_135, 2, x_122);
lean_ctor_set_uint8(x_135, 3, x_36);
if (lean_is_scalar(x_121)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_121;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_120);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec_ref(x_109);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_137 = lean_ctor_get(x_118, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_118, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_139 = x_118;
} else {
 lean_dec_ref(x_118);
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
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec_ref(x_35);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_141 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__11;
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_9);
return x_142;
}
block_32:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_19);
x_21 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1;
x_22 = l_Lean_MessageData_ofExpr(x_16);
x_23 = l_Lean_indentD(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Exception_toMessageData(x_10);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Tactic_evalRename___lam__0___closed__3;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_30, x_18, x_15, x_14, x_12, x_17, x_13, x_11);
lean_dec(x_13);
lean_dec_ref(x_17);
lean_dec(x_12);
lean_dec_ref(x_14);
lean_dec(x_15);
return x_31;
}
else
{
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_10);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabDecideConfig___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabDecideConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabDecideConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decide", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecide___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_13 = l_Lean_Elab_Tactic_elabDecideConfig___redArg(x_12, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Elab_Tactic_evalDecide___closed__1;
x_17 = l_Lean_Elab_Tactic_evalDecideCore(x_16, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalDecide(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalDecide___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalDecide", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0;
x_4 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecide___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(44u);
x_2 = lean_unsigned_to_nat(373u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(74u);
x_2 = lean_unsigned_to_nat(397u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(74u);
x_2 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(44u);
x_4 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(48u);
x_2 = lean_unsigned_to_nat(373u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(58u);
x_2 = lean_unsigned_to_nat(373u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(58u);
x_2 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(48u);
x_4 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2;
x_3 = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("native_decide", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalNativeDecide___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_13 = l_Lean_Elab_Tactic_elabDecideConfig___redArg(x_12, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 1;
lean_ctor_set_uint8(x_14, 1, x_17);
x_18 = l_Lean_Elab_Tactic_evalNativeDecide___closed__1;
x_19 = l_Lean_Elab_Tactic_evalDecideCore(x_18, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec_ref(x_14);
return x_19;
}
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get_uint8(x_14, 0);
x_21 = lean_ctor_get_uint8(x_14, 2);
x_22 = lean_ctor_get_uint8(x_14, 3);
lean_dec(x_14);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_24, 0, x_20);
lean_ctor_set_uint8(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, 2, x_21);
lean_ctor_set_uint8(x_24, 3, x_22);
x_25 = l_Lean_Elab_Tactic_evalNativeDecide___closed__1;
x_26 = l_Lean_Elab_Tactic_evalDecideCore(x_25, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec_ref(x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalNativeDecide(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nativeDecide", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalNativeDecide", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNativeDecide___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(50u);
x_2 = lean_unsigned_to_nat(410u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(160u);
x_2 = lean_unsigned_to_nat(417u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(160u);
x_2 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(50u);
x_4 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(54u);
x_2 = lean_unsigned_to_nat(410u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(70u);
x_2 = lean_unsigned_to_nat(410u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(70u);
x_2 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(54u);
x_4 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5;
x_2 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_ElabTerm(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Constructor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AuxLemma(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cleanup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__0);
l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__1 = _init_l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortTactic___at___Lean_Elab_Tactic_logUnassignedAndAbort_spec__0___redArg___closed__1);
l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0 = _init_l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_filterOldMVars___redArg___closed__0);
l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__0);
l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__1);
l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2 = _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__2);
l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3 = _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoalUsing___lam__0___closed__3);
l_Lean_Elab_Tactic_evalExact___closed__0 = _init_l_Lean_Elab_Tactic_evalExact___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___closed__0);
l_Lean_Elab_Tactic_evalExact___closed__1 = _init_l_Lean_Elab_Tactic_evalExact___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___closed__1);
l_Lean_Elab_Tactic_evalExact___closed__2 = _init_l_Lean_Elab_Tactic_evalExact___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___closed__2);
l_Lean_Elab_Tactic_evalExact___closed__3 = _init_l_Lean_Elab_Tactic_evalExact___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___closed__3);
l_Lean_Elab_Tactic_evalExact___closed__4 = _init_l_Lean_Elab_Tactic_evalExact___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___closed__4);
l_Lean_Elab_Tactic_evalExact___closed__5 = _init_l_Lean_Elab_Tactic_evalExact___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___closed__5);
l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__0);
l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1);
l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2);
l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3);
if (builtin) {res = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalExact___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_refineCore___lam__1___closed__0 = _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lam__1___closed__0);
l_Lean_Elab_Tactic_refineCore___lam__1___closed__1 = _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lam__1___closed__1);
l_Lean_Elab_Tactic_refineCore___lam__1___closed__2 = _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lam__1___closed__2);
l_Lean_Elab_Tactic_refineCore___lam__1___closed__3 = _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lam__1___closed__3);
l_Lean_Elab_Tactic_refineCore___lam__1___closed__4 = _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lam__1___closed__4);
l_Lean_Elab_Tactic_refineCore___lam__1___closed__5 = _init_l_Lean_Elab_Tactic_refineCore___lam__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lam__1___closed__5);
l_Lean_Elab_Tactic_evalRefine___closed__0 = _init_l_Lean_Elab_Tactic_evalRefine___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___closed__0);
l_Lean_Elab_Tactic_evalRefine___closed__1 = _init_l_Lean_Elab_Tactic_evalRefine___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___closed__1);
l_Lean_Elab_Tactic_evalRefine___closed__2 = _init_l_Lean_Elab_Tactic_evalRefine___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___closed__2);
l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0 = _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__0);
l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1 = _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1);
if (builtin) {res = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalRefine___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalRefine_x27___closed__0 = _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___closed__0);
l_Lean_Elab_Tactic_evalRefine_x27___closed__1 = _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___closed__1);
l_Lean_Elab_Tactic_evalRefine_x27___closed__2 = _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___closed__2);
l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0 = _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__0);
l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1 = _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1);
if (builtin) {res = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalRefine_x27___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__0);
l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___lam__0___closed__1);
l_Lean_Elab_Tactic_evalSpecialize___closed__0 = _init_l_Lean_Elab_Tactic_evalSpecialize___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___closed__0);
l_Lean_Elab_Tactic_evalSpecialize___closed__1 = _init_l_Lean_Elab_Tactic_evalSpecialize___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___closed__1);
l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0 = _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__0);
l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1 = _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1);
if (builtin) {res = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalSpecialize___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_elabTermForApply___closed__0 = _init_l_Lean_Elab_Tactic_elabTermForApply___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTermForApply___closed__0);
l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__0);
l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__1);
l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2 = _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__2);
l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3 = _init_l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarId___lam__0___closed__3);
l_Lean_Elab_Tactic_getFVarIds___boxed__const__1 = _init_l_Lean_Elab_Tactic_getFVarIds___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarIds___boxed__const__1);
l_Lean_Elab_Tactic_evalApply___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_evalApply___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___lam__0___closed__0);
l_Lean_Elab_Tactic_evalApply___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_evalApply___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___lam__0___closed__1);
l_Lean_Elab_Tactic_evalApply___closed__0 = _init_l_Lean_Elab_Tactic_evalApply___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___closed__0);
l_Lean_Elab_Tactic_evalApply___closed__1 = _init_l_Lean_Elab_Tactic_evalApply___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___closed__1);
l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0 = _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__0);
l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1 = _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1);
if (builtin) {res = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalApply___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___redArg___lam__0___closed__0);
l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__0);
l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1);
l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2);
l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3);
if (builtin) {res = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalConstructor___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalWithReducible___closed__0 = _init_l_Lean_Elab_Tactic_evalWithReducible___closed__0();
l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__0);
l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1);
l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2);
l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3);
if (builtin) {res = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalWithReducible___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___closed__0();
l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__0);
l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1);
l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2);
l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3);
if (builtin) {res = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalWithReducibleAndInstances___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___closed__0();
l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__0);
l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1);
l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2);
l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3);
if (builtin) {res = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalWithUnfoldingAll___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__0);
l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabAsFVar___lam__0___closed__1);
l_Lean_Elab_Tactic_evalRename___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___lam__0___closed__0);
l_Lean_Elab_Tactic_evalRename___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___lam__0___closed__1);
l_Lean_Elab_Tactic_evalRename___lam__0___closed__2 = _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___lam__0___closed__2);
l_Lean_Elab_Tactic_evalRename___lam__0___closed__3 = _init_l_Lean_Elab_Tactic_evalRename___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___lam__0___closed__3);
l_Lean_Elab_Tactic_evalRename___closed__0 = _init_l_Lean_Elab_Tactic_evalRename___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___closed__0);
l_Lean_Elab_Tactic_evalRename___closed__1 = _init_l_Lean_Elab_Tactic_evalRename___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___closed__1);
l_Lean_Elab_Tactic_evalRename___closed__2 = _init_l_Lean_Elab_Tactic_evalRename___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___closed__2);
l_Lean_Elab_Tactic_evalRename___closed__3 = _init_l_Lean_Elab_Tactic_evalRename___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___closed__3);
l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0 = _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__0);
l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1 = _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1);
if (builtin) {res = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalRename___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__0 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__0);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__1 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__1);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__2 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__2);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__3 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__3);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__4 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__4();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__4);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__5 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__5();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__5);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__6 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__6();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at___Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0_spec__0___redArg___closed__6);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__3);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__0 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__0);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__3 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__3);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__4 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__4);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__5 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__5);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__6 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__6);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__7 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__7);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__8 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__8);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__9 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___lam__0___closed__9);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__0 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__0);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__3 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__3);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__4 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__4);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__5 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__5);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__6 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__6);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__7 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__7);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__8 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__8);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__9 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__9);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__10 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__10);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__11 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__11);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__12 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__12);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__13 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__13);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__14 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__14);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__15 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__15);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__16 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__16);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__17 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__17);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__18 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__18);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__19 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__19();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__19);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__20 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__20();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__20);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__21 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__21();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__21);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__22 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__22();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__22);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__23 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__23();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__23);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__24 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__24();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__24);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__25 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__25();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__25);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__26 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__26();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__26);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__27 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__27();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__27);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___redArg___closed__28);
l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___closed__0 = _init_l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___closed__0();
lean_mark_persistent(l_Array_filterMapM___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___closed__0);
l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg___closed__0 = _init_l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg___closed__0();
lean_mark_persistent(l_Array_qsort_sort___at___Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___redArg___closed__0);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__0 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__0);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__1 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__1);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__2 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__2);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__3 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__1___closed__3);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__0 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__0);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__1 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__1);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__2 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__2);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__3 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__3);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__4 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__4);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__5 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__5);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__6 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__6);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__7 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__7);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__8 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__8);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__9 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__9);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__10 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__10);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__11 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__11);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__12 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__12);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__13 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__13);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__14 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__14);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__15 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__15);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__16 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__16);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__17 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__17);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__18 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__18);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__19 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__19);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__20 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__20);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__21 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__21();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__21);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__22 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__22();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__22);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__23 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__23();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__23);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__24 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__24();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__24);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__25 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__25();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__25);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__26 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__26();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__26);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__27 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__27();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__27);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__28 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__28();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__28);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__29 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__29();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__29);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__30 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__30();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__30);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__31 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__31();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__31);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__32 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__32();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__32);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__33 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__33();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__33);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__34 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__34();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__34);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__35 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__35();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__35);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__36 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__36();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__36);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__37 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__37();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__37);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__38 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__38();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__38);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__39 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__39();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__39);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__40 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__40();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__40);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__41 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__41();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__41);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__42 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__42();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__42);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__43 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__43();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__43);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__44 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__44();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__44);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__45 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__45();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__45);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__46 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__46();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__46);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__47 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__47();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__47);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__48 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__48();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__48);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__49 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__49();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__49);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__50 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__50();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__50);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__51 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__51();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__51);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__52 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__52();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__52);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__53 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__53();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__53);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__54 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__54();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__54);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__55 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__55();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__55);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__56 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__56();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__56);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__57 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__57();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___redArg___lam__2___closed__57);
l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0);
l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1);
l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_ = _init_l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__0____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_);
l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_ = _init_l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe___redArg___closed__1____x40_Lean_Elab_Tactic_ElabTerm___hyg_6042_);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__1);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__2);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__3);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__4);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__5);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__6);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__7);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__8);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__9);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__10);
l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__11 = _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__11);
l_Lean_Elab_Tactic_evalDecide___closed__0 = _init_l_Lean_Elab_Tactic_evalDecide___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___closed__0);
l_Lean_Elab_Tactic_evalDecide___closed__1 = _init_l_Lean_Elab_Tactic_evalDecide___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___closed__1);
l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0 = _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0);
l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1 = _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1);
l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2 = _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2);
if (builtin) {res = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalNativeDecide___closed__0 = _init_l_Lean_Elab_Tactic_evalNativeDecide___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___closed__0);
l_Lean_Elab_Tactic_evalNativeDecide___closed__1 = _init_l_Lean_Elab_Tactic_evalNativeDecide___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___closed__1);
l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0);
l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1);
l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2);
l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3);
if (builtin) {res = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0);
l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1);
l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2);
l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3);
l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4);
l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5);
l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6 = _init_l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
