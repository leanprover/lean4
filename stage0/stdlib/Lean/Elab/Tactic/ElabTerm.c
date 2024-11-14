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
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__12;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalConstructor___rarg___closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__4;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__5;
uint8_t l_Lean_MetavarKind_isNatural(uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__71;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__66;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__7;
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__4;
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__44;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLetRecAuxMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__52;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__48;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabDecideConfig___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideBang___closed__2;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__55;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore___closed__1;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__1;
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename__1(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__6;
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_Tactic_evalRename___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApply___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_runTermElab___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Tactic_refineCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__7;
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__1;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__6;
lean_object* l_Array_qpartition___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__53;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalApply___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__37;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Tactic_refineCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__1;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withoutRecover___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1;
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalRefine___closed__2;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__46;
static lean_object* l_Lean_Elab_Tactic_evalRename___lambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_refineCore___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__14;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__72;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_evalRename___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__2;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Elab_Tactic_evalRename___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__4;
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__3;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__78;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__2;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__43;
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__6;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__58;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__1;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__3;
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__54;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__4;
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__28;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__1;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__29;
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__5;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_filterOldMVars___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_filterOldMVars___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__68;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__27;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pushGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_checked_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__35;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__10;
lean_object* l_Lean_Elab_Tactic_popMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__2;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__24;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed__const__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__47;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__69;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_filterOldMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Elab_Tactic_evalRename___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__18;
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__8;
static lean_object* l_Lean_Elab_Tactic_evalRename___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__1;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__2;
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1;
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__16;
lean_object* l_outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3;
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_Tactic_evalDecideCore_doKernel___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__1;
lean_object* l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__9(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2(lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doElab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__38;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__8;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalRename___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__42;
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRename___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabTermForApply___closed__1;
static lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__4;
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine__1(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__7;
extern lean_object* l_Lean_MessageData_nil;
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__32;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1(lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecide___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__1;
lean_object* l_Lean_Option_set___at_Lean_Meta_getEqnsFor_x3f___spec__1(lean_object*, lean_object*, uint8_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__5;
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__2(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__21;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_refineCore___lambda__3___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_refineCore___lambda__3___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalDecideBang___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_refineCore___lambda__3___closed__6;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__15;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabDecideConfig___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__67;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__6;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__1;
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__3;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__60;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__2;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1(lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__74;
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__64;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__30;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__26;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__70;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_mkSimpCongrTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRefine___closed__1;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__1;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__17;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__79;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__5;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__45;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__39;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalApply___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__13;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__4;
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lambda__2(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalRefine___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalRename___closed__4;
lean_object* l_Lean_Meta_zetaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply__1(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__62;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__65;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__14;
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide__1(lean_object*);
static lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__7;
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_runTermElab___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__4;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__59;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__1;
uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_IR_IRType_beq___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___closed__3;
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_Tactic_evalDecideCore_doKernel___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__36;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__19;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaReduce___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__34;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalApply___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Elab_Tactic_refineCore___lambda__3___closed__3;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__50;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__5(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7;
static lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__49;
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__15;
static lean_object* l_Lean_Elab_Tactic_evalRefine_x27___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__61;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__22;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__13;
static lean_object* l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__31;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__73;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__25;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__51;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__40;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__3;
static lean_object* l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1;
uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__57;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__3;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__76;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_evalRename___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_evalRename___spec__7(lean_object*);
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__1;
lean_object* l_Lean_Meta_evalExpr_x27___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__4;
lean_object* l_Lean_Expr_headBeta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__23;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalExact___closed__1;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__3;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__56;
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__2;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__3;
lean_object* l_Lean_isDiagnosticsEnabled(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__2;
static lean_object* l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__1;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalNativeDecide___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__6;
lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__77;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__75;
static lean_object* l_Lean_Elab_Tactic_refineCore___lambda__3___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__41;
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__10;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__63;
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__3;
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__33;
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__3;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
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
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab_go___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_Tactic_runTermElab_go___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_runTermElab___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_1, x_2, x_3);
x_12 = l_Lean_Elab_Term_withoutErrToSorryImp___rarg(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_runTermElab___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_runTermElab___spec__1___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reuse stopped: guard failed at ", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_5, 8);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 8);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_5, 8, x_15);
x_16 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_23 = lean_ctor_get(x_5, 3);
x_24 = lean_ctor_get(x_5, 4);
x_25 = lean_ctor_get(x_5, 5);
x_26 = lean_ctor_get(x_5, 6);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_30 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_31 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_32 = lean_ctor_get(x_5, 7);
x_33 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
lean_inc(x_32);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_18);
lean_ctor_set(x_36, 2, x_19);
lean_ctor_set(x_36, 3, x_23);
lean_ctor_set(x_36, 4, x_24);
lean_ctor_set(x_36, 5, x_25);
lean_ctor_set(x_36, 6, x_26);
lean_ctor_set(x_36, 7, x_32);
lean_ctor_set(x_36, 8, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*9, x_20);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 1, x_21);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 2, x_22);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 3, x_27);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 4, x_28);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 5, x_29);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 6, x_30);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 7, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 8, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 9, x_34);
x_37 = lean_apply_9(x_2, x_3, x_4, x_36, x_6, x_7, x_8, x_9, x_10, x_11);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_5, 8);
lean_dec(x_42);
x_43 = lean_box(0);
x_44 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_12);
lean_dec(x_39);
x_45 = lean_box(0);
lean_ctor_set(x_5, 8, x_45);
x_46 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; 
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_5, 1);
x_50 = lean_ctor_get(x_5, 2);
x_51 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_52 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_53 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_54 = lean_ctor_get(x_5, 3);
x_55 = lean_ctor_get(x_5, 4);
x_56 = lean_ctor_get(x_5, 5);
x_57 = lean_ctor_get(x_5, 6);
x_58 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_59 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_60 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_61 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_62 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_63 = lean_ctor_get(x_5, 7);
x_64 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_65 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
lean_inc(x_63);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_5);
x_66 = lean_box(0);
x_67 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_12);
lean_dec(x_39);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_69, 0, x_48);
lean_ctor_set(x_69, 1, x_49);
lean_ctor_set(x_69, 2, x_50);
lean_ctor_set(x_69, 3, x_54);
lean_ctor_set(x_69, 4, x_55);
lean_ctor_set(x_69, 5, x_56);
lean_ctor_set(x_69, 6, x_57);
lean_ctor_set(x_69, 7, x_63);
lean_ctor_set(x_69, 8, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*9, x_51);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 1, x_52);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 2, x_53);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 3, x_58);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 4, x_59);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 5, x_60);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 6, x_61);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 7, x_62);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 8, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 9, x_65);
x_70 = lean_apply_9(x_2, x_3, x_4, x_69, x_6, x_7, x_8, x_9, x_10, x_11);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_71, 0, x_48);
lean_ctor_set(x_71, 1, x_49);
lean_ctor_set(x_71, 2, x_50);
lean_ctor_set(x_71, 3, x_54);
lean_ctor_set(x_71, 4, x_55);
lean_ctor_set(x_71, 5, x_56);
lean_ctor_set(x_71, 6, x_57);
lean_ctor_set(x_71, 7, x_63);
lean_ctor_set(x_71, 8, x_12);
lean_ctor_set_uint8(x_71, sizeof(void*)*9, x_51);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 1, x_52);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 2, x_53);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 3, x_58);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 4, x_59);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 5, x_60);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 6, x_61);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 7, x_62);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 8, x_64);
lean_ctor_set_uint8(x_71, sizeof(void*)*9 + 9, x_65);
x_72 = lean_apply_9(x_2, x_3, x_4, x_71, x_6, x_7, x_8, x_9, x_10, x_11);
return x_72;
}
}
}
else
{
lean_free_object(x_12);
if (x_1 == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_40);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_40, 0);
lean_dec(x_74);
x_75 = !lean_is_exclusive(x_5);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_5, 8);
lean_dec(x_76);
x_77 = lean_box(0);
x_78 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_free_object(x_40);
lean_dec(x_39);
x_79 = lean_box(0);
lean_ctor_set(x_5, 8, x_79);
x_80 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_80;
}
else
{
lean_object* x_81; 
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_5, 8, x_40);
x_81 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; lean_object* x_100; uint8_t x_101; 
x_82 = lean_ctor_get(x_5, 0);
x_83 = lean_ctor_get(x_5, 1);
x_84 = lean_ctor_get(x_5, 2);
x_85 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_86 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_87 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_88 = lean_ctor_get(x_5, 3);
x_89 = lean_ctor_get(x_5, 4);
x_90 = lean_ctor_get(x_5, 5);
x_91 = lean_ctor_get(x_5, 6);
x_92 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_93 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_94 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_95 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_96 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_97 = lean_ctor_get(x_5, 7);
x_98 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_99 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
lean_inc(x_97);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_5);
x_100 = lean_box(0);
x_101 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_40);
lean_dec(x_39);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_103, 0, x_82);
lean_ctor_set(x_103, 1, x_83);
lean_ctor_set(x_103, 2, x_84);
lean_ctor_set(x_103, 3, x_88);
lean_ctor_set(x_103, 4, x_89);
lean_ctor_set(x_103, 5, x_90);
lean_ctor_set(x_103, 6, x_91);
lean_ctor_set(x_103, 7, x_97);
lean_ctor_set(x_103, 8, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*9, x_85);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 1, x_86);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 2, x_87);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 3, x_92);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 4, x_93);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 5, x_94);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 6, x_95);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 7, x_96);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 8, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*9 + 9, x_99);
x_104 = lean_apply_9(x_2, x_3, x_4, x_103, x_6, x_7, x_8, x_9, x_10, x_11);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_ctor_set(x_40, 0, x_39);
x_105 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_105, 0, x_82);
lean_ctor_set(x_105, 1, x_83);
lean_ctor_set(x_105, 2, x_84);
lean_ctor_set(x_105, 3, x_88);
lean_ctor_set(x_105, 4, x_89);
lean_ctor_set(x_105, 5, x_90);
lean_ctor_set(x_105, 6, x_91);
lean_ctor_set(x_105, 7, x_97);
lean_ctor_set(x_105, 8, x_40);
lean_ctor_set_uint8(x_105, sizeof(void*)*9, x_85);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 1, x_86);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 2, x_87);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 3, x_92);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 4, x_93);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 5, x_94);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 6, x_95);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 7, x_96);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 8, x_98);
lean_ctor_set_uint8(x_105, sizeof(void*)*9 + 9, x_99);
x_106 = lean_apply_9(x_2, x_3, x_4, x_105, x_6, x_7, x_8, x_9, x_10, x_11);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_40);
x_107 = lean_ctor_get(x_5, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_5, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_5, 2);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_111 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_112 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_113 = lean_ctor_get(x_5, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_5, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_5, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_5, 6);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_118 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_119 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_120 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_121 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_122 = lean_ctor_get(x_5, 7);
lean_inc(x_122);
x_123 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_124 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 x_125 = x_5;
} else {
 lean_dec_ref(x_5);
 x_125 = lean_box(0);
}
x_126 = lean_box(0);
x_127 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_39);
x_128 = lean_box(0);
if (lean_is_scalar(x_125)) {
 x_129 = lean_alloc_ctor(0, 9, 10);
} else {
 x_129 = x_125;
}
lean_ctor_set(x_129, 0, x_107);
lean_ctor_set(x_129, 1, x_108);
lean_ctor_set(x_129, 2, x_109);
lean_ctor_set(x_129, 3, x_113);
lean_ctor_set(x_129, 4, x_114);
lean_ctor_set(x_129, 5, x_115);
lean_ctor_set(x_129, 6, x_116);
lean_ctor_set(x_129, 7, x_122);
lean_ctor_set(x_129, 8, x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*9, x_110);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 1, x_111);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 2, x_112);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 3, x_117);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 4, x_118);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 5, x_119);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 6, x_120);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 7, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 8, x_123);
lean_ctor_set_uint8(x_129, sizeof(void*)*9 + 9, x_124);
x_130 = lean_apply_9(x_2, x_3, x_4, x_129, x_6, x_7, x_8, x_9, x_10, x_11);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_39);
if (lean_is_scalar(x_125)) {
 x_132 = lean_alloc_ctor(0, 9, 10);
} else {
 x_132 = x_125;
}
lean_ctor_set(x_132, 0, x_107);
lean_ctor_set(x_132, 1, x_108);
lean_ctor_set(x_132, 2, x_109);
lean_ctor_set(x_132, 3, x_113);
lean_ctor_set(x_132, 4, x_114);
lean_ctor_set(x_132, 5, x_115);
lean_ctor_set(x_132, 6, x_116);
lean_ctor_set(x_132, 7, x_122);
lean_ctor_set(x_132, 8, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*9, x_110);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 1, x_111);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 2, x_112);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 3, x_117);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 4, x_118);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 5, x_119);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 6, x_120);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 7, x_121);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 8, x_123);
lean_ctor_set_uint8(x_132, sizeof(void*)*9 + 9, x_124);
x_133 = lean_apply_9(x_2, x_3, x_4, x_132, x_6, x_7, x_8, x_9, x_10, x_11);
return x_133;
}
}
}
else
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_5);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_5, 8);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_40);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_143; 
x_137 = lean_ctor_get(x_40, 0);
x_138 = lean_ctor_get(x_9, 2);
lean_inc(x_138);
x_139 = lean_box(x_1);
x_140 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_140, 0, x_139);
x_141 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__4;
x_142 = 0;
x_143 = l_Lean_KVMap_getBool(x_138, x_141, x_142);
lean_dec(x_138);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_140);
lean_dec(x_137);
x_144 = lean_box(0);
x_145 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_free_object(x_40);
lean_dec(x_39);
x_146 = lean_box(0);
lean_ctor_set(x_5, 8, x_146);
x_147 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_147;
}
else
{
lean_object* x_148; 
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_5, 8, x_40);
x_148 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_149 = lean_ctor_get(x_137, 0);
lean_inc(x_149);
lean_dec(x_137);
x_150 = lean_box(0);
x_151 = lean_unsigned_to_nat(0u);
x_152 = l_Lean_Syntax_formatStxAux(x_150, x_142, x_151, x_149);
x_153 = l_Std_Format_defWidth;
x_154 = lean_format_pretty(x_152, x_153, x_151, x_151);
x_155 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__5;
x_156 = lean_string_append(x_155, x_154);
lean_dec(x_154);
x_157 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__6;
x_158 = lean_string_append(x_156, x_157);
x_159 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_159, 0, x_140);
x_160 = lean_dbg_trace(x_158, x_159);
x_161 = lean_unbox(x_160);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; 
lean_free_object(x_40);
lean_dec(x_39);
lean_ctor_set(x_5, 8, x_150);
x_162 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_162;
}
else
{
lean_object* x_163; 
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_5, 8, x_40);
x_163 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; 
x_164 = lean_ctor_get(x_40, 0);
lean_inc(x_164);
lean_dec(x_40);
x_165 = lean_ctor_get(x_9, 2);
lean_inc(x_165);
x_166 = lean_box(x_1);
x_167 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_167, 0, x_166);
x_168 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__4;
x_169 = 0;
x_170 = l_Lean_KVMap_getBool(x_165, x_168, x_169);
lean_dec(x_165);
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; 
lean_dec(x_167);
lean_dec(x_164);
x_171 = lean_box(0);
x_172 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_39);
x_173 = lean_box(0);
lean_ctor_set(x_5, 8, x_173);
x_174 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_39);
lean_ctor_set(x_5, 8, x_175);
x_176 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_177 = lean_ctor_get(x_164, 0);
lean_inc(x_177);
lean_dec(x_164);
x_178 = lean_box(0);
x_179 = lean_unsigned_to_nat(0u);
x_180 = l_Lean_Syntax_formatStxAux(x_178, x_169, x_179, x_177);
x_181 = l_Std_Format_defWidth;
x_182 = lean_format_pretty(x_180, x_181, x_179, x_179);
x_183 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__5;
x_184 = lean_string_append(x_183, x_182);
lean_dec(x_182);
x_185 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__6;
x_186 = lean_string_append(x_184, x_185);
x_187 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_187, 0, x_167);
x_188 = lean_dbg_trace(x_186, x_187);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_39);
lean_ctor_set(x_5, 8, x_178);
x_190 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_39);
lean_ctor_set(x_5, 8, x_191);
x_192 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_192;
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_218; 
x_193 = lean_ctor_get(x_5, 0);
x_194 = lean_ctor_get(x_5, 1);
x_195 = lean_ctor_get(x_5, 2);
x_196 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_197 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_198 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_199 = lean_ctor_get(x_5, 3);
x_200 = lean_ctor_get(x_5, 4);
x_201 = lean_ctor_get(x_5, 5);
x_202 = lean_ctor_get(x_5, 6);
x_203 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_204 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_205 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_206 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_207 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_208 = lean_ctor_get(x_5, 7);
x_209 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_210 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
lean_inc(x_208);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_5);
x_211 = lean_ctor_get(x_40, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_212 = x_40;
} else {
 lean_dec_ref(x_40);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_9, 2);
lean_inc(x_213);
x_214 = lean_box(x_1);
x_215 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_215, 0, x_214);
x_216 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__4;
x_217 = 0;
x_218 = l_Lean_KVMap_getBool(x_213, x_216, x_217);
lean_dec(x_213);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; 
lean_dec(x_215);
lean_dec(x_211);
x_219 = lean_box(0);
x_220 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_212);
lean_dec(x_39);
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_222, 0, x_193);
lean_ctor_set(x_222, 1, x_194);
lean_ctor_set(x_222, 2, x_195);
lean_ctor_set(x_222, 3, x_199);
lean_ctor_set(x_222, 4, x_200);
lean_ctor_set(x_222, 5, x_201);
lean_ctor_set(x_222, 6, x_202);
lean_ctor_set(x_222, 7, x_208);
lean_ctor_set(x_222, 8, x_221);
lean_ctor_set_uint8(x_222, sizeof(void*)*9, x_196);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 1, x_197);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 2, x_198);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 3, x_203);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 4, x_204);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 5, x_205);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 6, x_206);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 7, x_207);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 8, x_209);
lean_ctor_set_uint8(x_222, sizeof(void*)*9 + 9, x_210);
x_223 = lean_apply_9(x_2, x_3, x_4, x_222, x_6, x_7, x_8, x_9, x_10, x_11);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
if (lean_is_scalar(x_212)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_212;
}
lean_ctor_set(x_224, 0, x_39);
x_225 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_225, 0, x_193);
lean_ctor_set(x_225, 1, x_194);
lean_ctor_set(x_225, 2, x_195);
lean_ctor_set(x_225, 3, x_199);
lean_ctor_set(x_225, 4, x_200);
lean_ctor_set(x_225, 5, x_201);
lean_ctor_set(x_225, 6, x_202);
lean_ctor_set(x_225, 7, x_208);
lean_ctor_set(x_225, 8, x_224);
lean_ctor_set_uint8(x_225, sizeof(void*)*9, x_196);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 1, x_197);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 2, x_198);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 3, x_203);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 4, x_204);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 5, x_205);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 6, x_206);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 7, x_207);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 8, x_209);
lean_ctor_set_uint8(x_225, sizeof(void*)*9 + 9, x_210);
x_226 = lean_apply_9(x_2, x_3, x_4, x_225, x_6, x_7, x_8, x_9, x_10, x_11);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_227 = lean_ctor_get(x_211, 0);
lean_inc(x_227);
lean_dec(x_211);
x_228 = lean_box(0);
x_229 = lean_unsigned_to_nat(0u);
x_230 = l_Lean_Syntax_formatStxAux(x_228, x_217, x_229, x_227);
x_231 = l_Std_Format_defWidth;
x_232 = lean_format_pretty(x_230, x_231, x_229, x_229);
x_233 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__5;
x_234 = lean_string_append(x_233, x_232);
lean_dec(x_232);
x_235 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__6;
x_236 = lean_string_append(x_234, x_235);
x_237 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_237, 0, x_215);
x_238 = lean_dbg_trace(x_236, x_237);
x_239 = lean_unbox(x_238);
lean_dec(x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_212);
lean_dec(x_39);
x_240 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_240, 0, x_193);
lean_ctor_set(x_240, 1, x_194);
lean_ctor_set(x_240, 2, x_195);
lean_ctor_set(x_240, 3, x_199);
lean_ctor_set(x_240, 4, x_200);
lean_ctor_set(x_240, 5, x_201);
lean_ctor_set(x_240, 6, x_202);
lean_ctor_set(x_240, 7, x_208);
lean_ctor_set(x_240, 8, x_228);
lean_ctor_set_uint8(x_240, sizeof(void*)*9, x_196);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 1, x_197);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 2, x_198);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 3, x_203);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 4, x_204);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 5, x_205);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 6, x_206);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 7, x_207);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 8, x_209);
lean_ctor_set_uint8(x_240, sizeof(void*)*9 + 9, x_210);
x_241 = lean_apply_9(x_2, x_3, x_4, x_240, x_6, x_7, x_8, x_9, x_10, x_11);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
if (lean_is_scalar(x_212)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_212;
}
lean_ctor_set(x_242, 0, x_39);
x_243 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_243, 0, x_193);
lean_ctor_set(x_243, 1, x_194);
lean_ctor_set(x_243, 2, x_195);
lean_ctor_set(x_243, 3, x_199);
lean_ctor_set(x_243, 4, x_200);
lean_ctor_set(x_243, 5, x_201);
lean_ctor_set(x_243, 6, x_202);
lean_ctor_set(x_243, 7, x_208);
lean_ctor_set(x_243, 8, x_242);
lean_ctor_set_uint8(x_243, sizeof(void*)*9, x_196);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 1, x_197);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 2, x_198);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 3, x_203);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 4, x_204);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 5, x_205);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 6, x_206);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 7, x_207);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 8, x_209);
lean_ctor_set_uint8(x_243, sizeof(void*)*9 + 9, x_210);
x_244 = lean_apply_9(x_2, x_3, x_4, x_243, x_6, x_7, x_8, x_9, x_10, x_11);
return x_244;
}
}
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_12, 0);
lean_inc(x_245);
lean_dec(x_12);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_258; uint8_t x_259; uint8_t x_260; uint8_t x_261; lean_object* x_262; uint8_t x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_247 = lean_ctor_get(x_5, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_5, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_5, 2);
lean_inc(x_249);
x_250 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_251 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_252 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_253 = lean_ctor_get(x_5, 3);
lean_inc(x_253);
x_254 = lean_ctor_get(x_5, 4);
lean_inc(x_254);
x_255 = lean_ctor_get(x_5, 5);
lean_inc(x_255);
x_256 = lean_ctor_get(x_5, 6);
lean_inc(x_256);
x_257 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_258 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_259 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_260 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_261 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_262 = lean_ctor_get(x_5, 7);
lean_inc(x_262);
x_263 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_264 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 x_265 = x_5;
} else {
 lean_dec_ref(x_5);
 x_265 = lean_box(0);
}
x_266 = lean_box(0);
x_267 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_245);
x_268 = lean_box(0);
if (lean_is_scalar(x_265)) {
 x_269 = lean_alloc_ctor(0, 9, 10);
} else {
 x_269 = x_265;
}
lean_ctor_set(x_269, 0, x_247);
lean_ctor_set(x_269, 1, x_248);
lean_ctor_set(x_269, 2, x_249);
lean_ctor_set(x_269, 3, x_253);
lean_ctor_set(x_269, 4, x_254);
lean_ctor_set(x_269, 5, x_255);
lean_ctor_set(x_269, 6, x_256);
lean_ctor_set(x_269, 7, x_262);
lean_ctor_set(x_269, 8, x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*9, x_250);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 1, x_251);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 2, x_252);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 3, x_257);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 4, x_258);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 5, x_259);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 6, x_260);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 7, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 8, x_263);
lean_ctor_set_uint8(x_269, sizeof(void*)*9 + 9, x_264);
x_270 = lean_apply_9(x_2, x_3, x_4, x_269, x_6, x_7, x_8, x_9, x_10, x_11);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_245);
if (lean_is_scalar(x_265)) {
 x_272 = lean_alloc_ctor(0, 9, 10);
} else {
 x_272 = x_265;
}
lean_ctor_set(x_272, 0, x_247);
lean_ctor_set(x_272, 1, x_248);
lean_ctor_set(x_272, 2, x_249);
lean_ctor_set(x_272, 3, x_253);
lean_ctor_set(x_272, 4, x_254);
lean_ctor_set(x_272, 5, x_255);
lean_ctor_set(x_272, 6, x_256);
lean_ctor_set(x_272, 7, x_262);
lean_ctor_set(x_272, 8, x_271);
lean_ctor_set_uint8(x_272, sizeof(void*)*9, x_250);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 1, x_251);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 2, x_252);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 3, x_257);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 4, x_258);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 5, x_259);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 6, x_260);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 7, x_261);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 8, x_263);
lean_ctor_set_uint8(x_272, sizeof(void*)*9 + 9, x_264);
x_273 = lean_apply_9(x_2, x_3, x_4, x_272, x_6, x_7, x_8, x_9, x_10, x_11);
return x_273;
}
}
else
{
if (x_1 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_286; uint8_t x_287; uint8_t x_288; uint8_t x_289; lean_object* x_290; uint8_t x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_274 = x_246;
} else {
 lean_dec_ref(x_246);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_5, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_5, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_5, 2);
lean_inc(x_277);
x_278 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_279 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_280 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_281 = lean_ctor_get(x_5, 3);
lean_inc(x_281);
x_282 = lean_ctor_get(x_5, 4);
lean_inc(x_282);
x_283 = lean_ctor_get(x_5, 5);
lean_inc(x_283);
x_284 = lean_ctor_get(x_5, 6);
lean_inc(x_284);
x_285 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_286 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_287 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_288 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_289 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_290 = lean_ctor_get(x_5, 7);
lean_inc(x_290);
x_291 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_292 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 x_293 = x_5;
} else {
 lean_dec_ref(x_5);
 x_293 = lean_box(0);
}
x_294 = lean_box(0);
x_295 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_274);
lean_dec(x_245);
x_296 = lean_box(0);
if (lean_is_scalar(x_293)) {
 x_297 = lean_alloc_ctor(0, 9, 10);
} else {
 x_297 = x_293;
}
lean_ctor_set(x_297, 0, x_275);
lean_ctor_set(x_297, 1, x_276);
lean_ctor_set(x_297, 2, x_277);
lean_ctor_set(x_297, 3, x_281);
lean_ctor_set(x_297, 4, x_282);
lean_ctor_set(x_297, 5, x_283);
lean_ctor_set(x_297, 6, x_284);
lean_ctor_set(x_297, 7, x_290);
lean_ctor_set(x_297, 8, x_296);
lean_ctor_set_uint8(x_297, sizeof(void*)*9, x_278);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 1, x_279);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 2, x_280);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 3, x_285);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 4, x_286);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 5, x_287);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 6, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 7, x_289);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 8, x_291);
lean_ctor_set_uint8(x_297, sizeof(void*)*9 + 9, x_292);
x_298 = lean_apply_9(x_2, x_3, x_4, x_297, x_6, x_7, x_8, x_9, x_10, x_11);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
if (lean_is_scalar(x_274)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_274;
}
lean_ctor_set(x_299, 0, x_245);
if (lean_is_scalar(x_293)) {
 x_300 = lean_alloc_ctor(0, 9, 10);
} else {
 x_300 = x_293;
}
lean_ctor_set(x_300, 0, x_275);
lean_ctor_set(x_300, 1, x_276);
lean_ctor_set(x_300, 2, x_277);
lean_ctor_set(x_300, 3, x_281);
lean_ctor_set(x_300, 4, x_282);
lean_ctor_set(x_300, 5, x_283);
lean_ctor_set(x_300, 6, x_284);
lean_ctor_set(x_300, 7, x_290);
lean_ctor_set(x_300, 8, x_299);
lean_ctor_set_uint8(x_300, sizeof(void*)*9, x_278);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 1, x_279);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 2, x_280);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 3, x_285);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 4, x_286);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 5, x_287);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 6, x_288);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 7, x_289);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 8, x_291);
lean_ctor_set_uint8(x_300, sizeof(void*)*9 + 9, x_292);
x_301 = lean_apply_9(x_2, x_3, x_4, x_300, x_6, x_7, x_8, x_9, x_10, x_11);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_313; uint8_t x_314; uint8_t x_315; uint8_t x_316; lean_object* x_317; uint8_t x_318; uint8_t x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_328; 
x_302 = lean_ctor_get(x_5, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_5, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_5, 2);
lean_inc(x_304);
x_305 = lean_ctor_get_uint8(x_5, sizeof(void*)*9);
x_306 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 1);
x_307 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 2);
x_308 = lean_ctor_get(x_5, 3);
lean_inc(x_308);
x_309 = lean_ctor_get(x_5, 4);
lean_inc(x_309);
x_310 = lean_ctor_get(x_5, 5);
lean_inc(x_310);
x_311 = lean_ctor_get(x_5, 6);
lean_inc(x_311);
x_312 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 3);
x_313 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 4);
x_314 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 5);
x_315 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 6);
x_316 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 7);
x_317 = lean_ctor_get(x_5, 7);
lean_inc(x_317);
x_318 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 8);
x_319 = lean_ctor_get_uint8(x_5, sizeof(void*)*9 + 9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 x_320 = x_5;
} else {
 lean_dec_ref(x_5);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_246, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_322 = x_246;
} else {
 lean_dec_ref(x_246);
 x_322 = lean_box(0);
}
x_323 = lean_ctor_get(x_9, 2);
lean_inc(x_323);
x_324 = lean_box(x_1);
x_325 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_325, 0, x_324);
x_326 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__4;
x_327 = 0;
x_328 = l_Lean_KVMap_getBool(x_323, x_326, x_327);
lean_dec(x_323);
if (x_328 == 0)
{
lean_object* x_329; uint8_t x_330; 
lean_dec(x_325);
lean_dec(x_321);
x_329 = lean_box(0);
x_330 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_1, x_329);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_322);
lean_dec(x_245);
x_331 = lean_box(0);
if (lean_is_scalar(x_320)) {
 x_332 = lean_alloc_ctor(0, 9, 10);
} else {
 x_332 = x_320;
}
lean_ctor_set(x_332, 0, x_302);
lean_ctor_set(x_332, 1, x_303);
lean_ctor_set(x_332, 2, x_304);
lean_ctor_set(x_332, 3, x_308);
lean_ctor_set(x_332, 4, x_309);
lean_ctor_set(x_332, 5, x_310);
lean_ctor_set(x_332, 6, x_311);
lean_ctor_set(x_332, 7, x_317);
lean_ctor_set(x_332, 8, x_331);
lean_ctor_set_uint8(x_332, sizeof(void*)*9, x_305);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 1, x_306);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 2, x_307);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 3, x_312);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 4, x_313);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 5, x_314);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 6, x_315);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 7, x_316);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 8, x_318);
lean_ctor_set_uint8(x_332, sizeof(void*)*9 + 9, x_319);
x_333 = lean_apply_9(x_2, x_3, x_4, x_332, x_6, x_7, x_8, x_9, x_10, x_11);
return x_333;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
if (lean_is_scalar(x_322)) {
 x_334 = lean_alloc_ctor(1, 1, 0);
} else {
 x_334 = x_322;
}
lean_ctor_set(x_334, 0, x_245);
if (lean_is_scalar(x_320)) {
 x_335 = lean_alloc_ctor(0, 9, 10);
} else {
 x_335 = x_320;
}
lean_ctor_set(x_335, 0, x_302);
lean_ctor_set(x_335, 1, x_303);
lean_ctor_set(x_335, 2, x_304);
lean_ctor_set(x_335, 3, x_308);
lean_ctor_set(x_335, 4, x_309);
lean_ctor_set(x_335, 5, x_310);
lean_ctor_set(x_335, 6, x_311);
lean_ctor_set(x_335, 7, x_317);
lean_ctor_set(x_335, 8, x_334);
lean_ctor_set_uint8(x_335, sizeof(void*)*9, x_305);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 1, x_306);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 2, x_307);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 3, x_312);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 4, x_313);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 5, x_314);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 6, x_315);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 7, x_316);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 8, x_318);
lean_ctor_set_uint8(x_335, sizeof(void*)*9 + 9, x_319);
x_336 = lean_apply_9(x_2, x_3, x_4, x_335, x_6, x_7, x_8, x_9, x_10, x_11);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_337 = lean_ctor_get(x_321, 0);
lean_inc(x_337);
lean_dec(x_321);
x_338 = lean_box(0);
x_339 = lean_unsigned_to_nat(0u);
x_340 = l_Lean_Syntax_formatStxAux(x_338, x_327, x_339, x_337);
x_341 = l_Std_Format_defWidth;
x_342 = lean_format_pretty(x_340, x_341, x_339, x_339);
x_343 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__5;
x_344 = lean_string_append(x_343, x_342);
lean_dec(x_342);
x_345 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__6;
x_346 = lean_string_append(x_344, x_345);
x_347 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_347, 0, x_325);
x_348 = lean_dbg_trace(x_346, x_347);
x_349 = lean_unbox(x_348);
lean_dec(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_322);
lean_dec(x_245);
if (lean_is_scalar(x_320)) {
 x_350 = lean_alloc_ctor(0, 9, 10);
} else {
 x_350 = x_320;
}
lean_ctor_set(x_350, 0, x_302);
lean_ctor_set(x_350, 1, x_303);
lean_ctor_set(x_350, 2, x_304);
lean_ctor_set(x_350, 3, x_308);
lean_ctor_set(x_350, 4, x_309);
lean_ctor_set(x_350, 5, x_310);
lean_ctor_set(x_350, 6, x_311);
lean_ctor_set(x_350, 7, x_317);
lean_ctor_set(x_350, 8, x_338);
lean_ctor_set_uint8(x_350, sizeof(void*)*9, x_305);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 1, x_306);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 2, x_307);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 3, x_312);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 4, x_313);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 5, x_314);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 6, x_315);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 7, x_316);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 8, x_318);
lean_ctor_set_uint8(x_350, sizeof(void*)*9 + 9, x_319);
x_351 = lean_apply_9(x_2, x_3, x_4, x_350, x_6, x_7, x_8, x_9, x_10, x_11);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
if (lean_is_scalar(x_322)) {
 x_352 = lean_alloc_ctor(1, 1, 0);
} else {
 x_352 = x_322;
}
lean_ctor_set(x_352, 0, x_245);
if (lean_is_scalar(x_320)) {
 x_353 = lean_alloc_ctor(0, 9, 10);
} else {
 x_353 = x_320;
}
lean_ctor_set(x_353, 0, x_302);
lean_ctor_set(x_353, 1, x_303);
lean_ctor_set(x_353, 2, x_304);
lean_ctor_set(x_353, 3, x_308);
lean_ctor_set(x_353, 4, x_309);
lean_ctor_set(x_353, 5, x_310);
lean_ctor_set(x_353, 6, x_311);
lean_ctor_set(x_353, 7, x_317);
lean_ctor_set(x_353, 8, x_352);
lean_ctor_set_uint8(x_353, sizeof(void*)*9, x_305);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 1, x_306);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 2, x_307);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 3, x_312);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 4, x_313);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 5, x_314);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 6, x_315);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 7, x_316);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 8, x_318);
lean_ctor_set_uint8(x_353, sizeof(void*)*9 + 9, x_319);
x_354 = lean_apply_9(x_2, x_3, x_4, x_353, x_6, x_7, x_8, x_9, x_10, x_11);
return x_354;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_runTermElab_go___rarg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___rarg___lambda__1___boxed), 11, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_Tactic_runTermElab___spec__1___rarg(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = l_Lean_Elab_Tactic_runTermElab_go___rarg(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_box(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___rarg___lambda__2___boxed), 11, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = 1;
x_15 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg(x_14, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_runTermElab___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_runTermElab___rarg___lambda__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_runTermElab___rarg___lambda__2(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_runTermElab___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_runTermElab___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_box(x_13);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_15);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 5);
x_19 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
lean_dec(x_1);
lean_ctor_set(x_10, 5, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Elab_Tactic_runTermElab___rarg(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
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
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
x_30 = lean_ctor_get(x_10, 2);
x_31 = lean_ctor_get(x_10, 3);
x_32 = lean_ctor_get(x_10, 4);
x_33 = lean_ctor_get(x_10, 5);
x_34 = lean_ctor_get(x_10, 6);
x_35 = lean_ctor_get(x_10, 7);
x_36 = lean_ctor_get(x_10, 8);
x_37 = lean_ctor_get(x_10, 9);
x_38 = lean_ctor_get(x_10, 10);
x_39 = lean_ctor_get_uint8(x_10, sizeof(void*)*12);
x_40 = lean_ctor_get(x_10, 11);
x_41 = lean_ctor_get_uint8(x_10, sizeof(void*)*12 + 1);
lean_inc(x_40);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_42 = l_Lean_replaceRef(x_1, x_33);
lean_dec(x_33);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_29);
lean_ctor_set(x_43, 2, x_30);
lean_ctor_set(x_43, 3, x_31);
lean_ctor_set(x_43, 4, x_32);
lean_ctor_set(x_43, 5, x_42);
lean_ctor_set(x_43, 6, x_34);
lean_ctor_set(x_43, 7, x_35);
lean_ctor_set(x_43, 8, x_36);
lean_ctor_set(x_43, 9, x_37);
lean_ctor_set(x_43, 10, x_38);
lean_ctor_set(x_43, 11, x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*12, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*12 + 1, x_41);
lean_inc(x_11);
lean_inc(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_44 = l_Lean_Elab_Tactic_runTermElab___rarg(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_43, x_11, x_12);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_43, x_11, x_46);
lean_dec(x_11);
lean_dec(x_43);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_13 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_18);
x_21 = lean_infer_type(x_18, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_8, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 5);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
x_32 = lean_ctor_get_uint8(x_8, sizeof(void*)*6 + 1);
x_33 = 1;
lean_ctor_set_uint8(x_22, 7, x_33);
x_34 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*6, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*6 + 1, x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_20);
lean_inc(x_23);
x_35 = l_Lean_Meta_isExprDefEq(x_23, x_20, x_34, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_39, x_20, x_23, x_18, x_39, x_39, x_8, x_9, x_10, x_11, x_38);
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
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_35, 0);
lean_dec(x_46);
lean_ctor_set(x_35, 0, x_18);
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_dec(x_35);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_53 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
x_54 = lean_ctor_get_uint8(x_8, sizeof(void*)*6 + 1);
x_55 = lean_ctor_get_uint8(x_22, 0);
x_56 = lean_ctor_get_uint8(x_22, 1);
x_57 = lean_ctor_get_uint8(x_22, 2);
x_58 = lean_ctor_get_uint8(x_22, 3);
x_59 = lean_ctor_get_uint8(x_22, 4);
x_60 = lean_ctor_get_uint8(x_22, 5);
x_61 = lean_ctor_get_uint8(x_22, 6);
x_62 = lean_ctor_get_uint8(x_22, 8);
x_63 = lean_ctor_get_uint8(x_22, 9);
x_64 = lean_ctor_get_uint8(x_22, 10);
x_65 = lean_ctor_get_uint8(x_22, 11);
x_66 = lean_ctor_get_uint8(x_22, 12);
lean_dec(x_22);
x_67 = 1;
x_68 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_68, 0, x_55);
lean_ctor_set_uint8(x_68, 1, x_56);
lean_ctor_set_uint8(x_68, 2, x_57);
lean_ctor_set_uint8(x_68, 3, x_58);
lean_ctor_set_uint8(x_68, 4, x_59);
lean_ctor_set_uint8(x_68, 5, x_60);
lean_ctor_set_uint8(x_68, 6, x_61);
lean_ctor_set_uint8(x_68, 7, x_67);
lean_ctor_set_uint8(x_68, 8, x_62);
lean_ctor_set_uint8(x_68, 9, x_63);
lean_ctor_set_uint8(x_68, 10, x_64);
lean_ctor_set_uint8(x_68, 11, x_65);
lean_ctor_set_uint8(x_68, 12, x_66);
x_69 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_25);
lean_ctor_set(x_69, 2, x_26);
lean_ctor_set(x_69, 3, x_27);
lean_ctor_set(x_69, 4, x_28);
lean_ctor_set(x_69, 5, x_29);
lean_ctor_set_uint8(x_69, sizeof(void*)*6, x_53);
lean_ctor_set_uint8(x_69, sizeof(void*)*6 + 1, x_54);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_20);
lean_inc(x_23);
x_70 = l_Lean_Meta_isExprDefEq(x_23, x_20, x_69, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_box(0);
x_75 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_74, x_20, x_23, x_18, x_74, x_74, x_8, x_9, x_10, x_11, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
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
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_81 = x_70;
} else {
 lean_dec_ref(x_70);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_18);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_83 = lean_ctor_get(x_70, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_70, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_85 = x_70;
} else {
 lean_dec_ref(x_70);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_87 = !lean_is_exclusive(x_21);
if (x_87 == 0)
{
return x_21;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_21, 0);
x_89 = lean_ctor_get(x_21, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_21);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_13);
if (x_91 == 0)
{
return x_13;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_13, 0);
x_93 = lean_ctor_get(x_13, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_13);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_elabTermEnsuringType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermEnsuringType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_Tactic_elabTermEnsuringType(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_abortTacticExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg), 1, 0);
return x_9;
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
lean_dec(x_12);
x_22 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg(x_21);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_logUnassignedAndAbort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_filterOldMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
x_9 = l_Lean_MetavarContext_getDecl(x_2, x_8);
x_10 = lean_ctor_get(x_9, 6);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_nat_dec_le(x_1, x_10);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_4, x_12);
if (x_11 == 0)
{
lean_dec(x_8);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_6, x_8);
x_4 = x_13;
x_6 = x_15;
goto _start;
}
}
else
{
lean_dec(x_2);
return x_6;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_filterOldMVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
x_15 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_12, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_20 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_filterOldMVars___spec__1(x_2, x_11, x_1, x_18, x_19, x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_24);
x_28 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_25, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_24);
x_31 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_filterOldMVars___spec__1(x_2, x_24, x_1, x_33, x_34, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_filterOldMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_filterOldMVars___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_filterOldMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_filterOldMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("attempting to close the goal using", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nthis is often due occurs-check failure", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_14 = lean_checked_assign(x_1, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_indentExpr(x_2);
x_19 = l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_1, x_23, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_14, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_dec(x_15);
lean_inc(x_1);
x_18 = l_Lean_MVarId_getTag(x_1, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = lean_apply_11(x_2, x_16, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_21) == 0)
{
if (x_4 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1(x_1, x_22, x_3, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
lean_inc(x_26);
x_28 = l_Lean_Meta_getMVars(x_26, x_10, x_11, x_12, x_13, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Tactic_filterOldMVars(x_29, x_5, x_10, x_11, x_12, x_13, x_30);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_34 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1(x_1, x_26, x_3, x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_35);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_18);
if (x_46 == 0)
{
return x_18;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_18, 0);
x_48 = lean_ctor_get(x_18, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_18);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_15, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_15);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_st_ref_get(x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Tactic_popMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(x_3);
lean_inc(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__2___boxed), 14, 5);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_21);
lean_closure_set(x_22, 4, x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
x_23 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_19, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_19);
lean_dec(x_11);
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
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_Exception_isInterrupt(x_25);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Exception_isRuntime(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
lean_free_object(x_23);
x_29 = l_Lean_Elab_Tactic_pushGoal(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_25);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = l_Lean_Exception_isInterrupt(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Exception_isRuntime(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = l_Lean_Elab_Tactic_pushGoal(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
 lean_ctor_set_tag(x_41, 1);
}
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_35);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_17);
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
x_44 = !lean_is_exclusive(x_18);
if (x_44 == 0)
{
return x_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__2(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_closeMainGoalUsing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_Tactic_closeMainGoalUsing(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l_Lean_Elab_Tactic_evalExact___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExact___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalExact___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalExact___closed__5;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact___lambda__1___boxed), 12, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Tactic_evalExact___closed__6;
x_18 = 1;
x_19 = l_Lean_Elab_Tactic_closeMainGoalUsing(x_17, x_16, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExact___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalExact___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalExact", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExact), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(71u);
x_2 = lean_unsigned_to_nat(26u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(78u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(26u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(71u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(71u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(30u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(39u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_4 = l_Lean_MetavarContext_getDecl(x_1, x_2);
x_5 = l_Lean_MetavarContext_getDecl(x_1, x_3);
x_6 = lean_ctor_get(x_4, 6);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 6);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = l_Lean_Name_quickLt(x_2, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_3);
x_7 = l_Array_qpartition___rarg(x_2, x_5, x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_le(x_4, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_11 = l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1(x_1, x_9, x_3, x_8);
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
lean_dec(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_get_size(x_2);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1(x_3, x_2, x_9, x_8);
lean_dec(x_8);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_to_list(x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_array_mk(x_3);
lean_inc(x_2);
x_6 = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___rarg(x_1, x_2, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdsByIndex___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_sortMVarIdsByIndex___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at_Lean_Elab_Tactic_sortMVarIdArrayByIndex___spec__1___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_3);
x_7 = l_Array_qpartition___rarg(x_2, x_5, x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_le(x_4, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_11 = l_Array_qsort_sort___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__3(x_1, x_9, x_3, x_8);
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
lean_dec(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_array_get_size(x_1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_15, x_16);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_qsort_sort___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__3(x_14, x_1, x_18, x_17);
lean_dec(x_17);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_qsort_sort___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__3(x_22, x_1, x_26, x_25);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_mk(x_1);
x_12 = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_1, x_2);
lean_inc(x_15);
x_16 = l_Lean_MVarId_getKind(x_15, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unbox(x_17);
lean_dec(x_17);
x_20 = l_Lean_MetavarKind_isNatural(x_19);
if (x_20 == 0)
{
size_t x_21; size_t x_22; 
lean_dec(x_15);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_13 = x_18;
goto _start;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_array_push(x_4, x_15);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_2 = x_26;
x_4 = x_24;
x_13 = x_18;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_uget(x_1, x_2);
lean_inc(x_15);
x_16 = l_Lean_Elab_Term_isLetRecAuxMVar(x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_push(x_4, x_15);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_2 = x_22;
x_4 = x_20;
x_13 = x_19;
goto _start;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_15);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_2 = x_26;
x_13 = x_24;
goto _start;
}
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_13);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_to_list(x_1);
x_16 = l_Lean_Elab_Tactic_sortMVarIdsByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__1(x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_20 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_2, x_3, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
lean_inc(x_25);
x_27 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_2, x_3, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_25);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_st_ref_get(x_10, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = lean_apply_9(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_20);
x_22 = l_Lean_Meta_getMVarsNoDelayed(x_20, x_9, x_10, x_11, x_12, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
if (x_27 == 0)
{
lean_object* x_77; 
lean_dec(x_25);
lean_dec(x_23);
x_77 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_28 = x_77;
x_29 = x_24;
goto block_76;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_25, x_25);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_25);
lean_dec(x_23);
x_79 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_28 = x_79;
x_29 = x_24;
goto block_76;
}
else
{
size_t x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = 0;
x_81 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_82 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_83 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__5(x_23, x_80, x_81, x_82, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_23);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_28 = x_84;
x_29 = x_85;
goto block_76;
}
}
block_76:
{
lean_object* x_30; 
x_30 = l_Lean_Elab_Tactic_filterOldMVars(x_28, x_18, x_9, x_10, x_11, x_12, x_29);
lean_dec(x_18);
lean_dec(x_28);
if (x_4 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_31);
x_34 = lean_nat_dec_lt(x_26, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_33);
x_35 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___lambda__1(x_31, x_2, x_3, x_20, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_38);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_37);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
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
x_44 = lean_nat_dec_le(x_33, x_33);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_33);
x_45 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_46 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___lambda__1(x_31, x_2, x_3, x_20, x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_48);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_47);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; lean_object* x_57; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_56 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_57 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__4(x_31, x_54, x_55, x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_60 = l_Lean_Elab_Tactic_logUnassignedAndAbort(x_58, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_59);
lean_dec(x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___lambda__1(x_31, x_2, x_3, x_20, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_62);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_61);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 0);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_60);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_57);
if (x_68 == 0)
{
return x_57;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_57, 0);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_57);
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
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_30, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_30, 1);
lean_inc(x_73);
lean_dec(x_30);
x_74 = lean_box(0);
x_75 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___lambda__1(x_72, x_2, x_3, x_20, x_74, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_73);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_75;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_19);
if (x_86 == 0)
{
return x_19;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_19, 0);
x_88 = lean_ctor_get(x_19, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_19);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_sortMVarIdArrayByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_sortMVarIdsByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_sortMVarIdsByIndex___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__4(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___spec__5(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
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
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 9);
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
lean_ctor_set_uint8(x_15, 7, x_21);
if (x_18 == 0)
{
lean_object* x_22; 
lean_ctor_set_uint8(x_7, sizeof(void*)*9 + 9, x_4);
x_22 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
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
else
{
lean_object* x_31; 
lean_ctor_set_uint8(x_7, sizeof(void*)*9 + 9, x_21);
x_31 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
}
else
{
uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_40 = lean_ctor_get_uint8(x_15, 0);
x_41 = lean_ctor_get_uint8(x_15, 1);
x_42 = lean_ctor_get_uint8(x_15, 2);
x_43 = lean_ctor_get_uint8(x_15, 3);
x_44 = lean_ctor_get_uint8(x_15, 4);
x_45 = lean_ctor_get_uint8(x_15, 5);
x_46 = lean_ctor_get_uint8(x_15, 6);
x_47 = lean_ctor_get_uint8(x_15, 8);
x_48 = lean_ctor_get_uint8(x_15, 9);
x_49 = lean_ctor_get_uint8(x_15, 10);
x_50 = lean_ctor_get_uint8(x_15, 11);
x_51 = lean_ctor_get_uint8(x_15, 12);
lean_dec(x_15);
x_52 = 1;
x_53 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_53, 0, x_40);
lean_ctor_set_uint8(x_53, 1, x_41);
lean_ctor_set_uint8(x_53, 2, x_42);
lean_ctor_set_uint8(x_53, 3, x_43);
lean_ctor_set_uint8(x_53, 4, x_44);
lean_ctor_set_uint8(x_53, 5, x_45);
lean_ctor_set_uint8(x_53, 6, x_46);
lean_ctor_set_uint8(x_53, 7, x_52);
lean_ctor_set_uint8(x_53, 8, x_47);
lean_ctor_set_uint8(x_53, 9, x_48);
lean_ctor_set_uint8(x_53, 10, x_49);
lean_ctor_set_uint8(x_53, 11, x_50);
lean_ctor_set_uint8(x_53, 12, x_51);
lean_ctor_set(x_9, 0, x_53);
if (x_18 == 0)
{
lean_object* x_54; 
lean_ctor_set_uint8(x_7, sizeof(void*)*9 + 9, x_4);
x_54 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
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
else
{
lean_object* x_63; 
lean_ctor_set_uint8(x_7, sizeof(void*)*9 + 9, x_52);
x_63 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_70 = x_63;
} else {
 lean_dec_ref(x_63);
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
}
else
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_72 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 9);
x_73 = lean_ctor_get(x_9, 1);
x_74 = lean_ctor_get(x_9, 2);
x_75 = lean_ctor_get(x_9, 3);
x_76 = lean_ctor_get(x_9, 4);
x_77 = lean_ctor_get(x_9, 5);
x_78 = lean_ctor_get_uint8(x_9, sizeof(void*)*6);
x_79 = lean_ctor_get_uint8(x_9, sizeof(void*)*6 + 1);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_9);
x_80 = lean_ctor_get_uint8(x_15, 0);
x_81 = lean_ctor_get_uint8(x_15, 1);
x_82 = lean_ctor_get_uint8(x_15, 2);
x_83 = lean_ctor_get_uint8(x_15, 3);
x_84 = lean_ctor_get_uint8(x_15, 4);
x_85 = lean_ctor_get_uint8(x_15, 5);
x_86 = lean_ctor_get_uint8(x_15, 6);
x_87 = lean_ctor_get_uint8(x_15, 8);
x_88 = lean_ctor_get_uint8(x_15, 9);
x_89 = lean_ctor_get_uint8(x_15, 10);
x_90 = lean_ctor_get_uint8(x_15, 11);
x_91 = lean_ctor_get_uint8(x_15, 12);
if (lean_is_exclusive(x_15)) {
 x_92 = x_15;
} else {
 lean_dec_ref(x_15);
 x_92 = lean_box(0);
}
x_93 = 1;
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 0, 13);
} else {
 x_94 = x_92;
}
lean_ctor_set_uint8(x_94, 0, x_80);
lean_ctor_set_uint8(x_94, 1, x_81);
lean_ctor_set_uint8(x_94, 2, x_82);
lean_ctor_set_uint8(x_94, 3, x_83);
lean_ctor_set_uint8(x_94, 4, x_84);
lean_ctor_set_uint8(x_94, 5, x_85);
lean_ctor_set_uint8(x_94, 6, x_86);
lean_ctor_set_uint8(x_94, 7, x_93);
lean_ctor_set_uint8(x_94, 8, x_87);
lean_ctor_set_uint8(x_94, 9, x_88);
lean_ctor_set_uint8(x_94, 10, x_89);
lean_ctor_set_uint8(x_94, 11, x_90);
lean_ctor_set_uint8(x_94, 12, x_91);
x_95 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_73);
lean_ctor_set(x_95, 2, x_74);
lean_ctor_set(x_95, 3, x_75);
lean_ctor_set(x_95, 4, x_76);
lean_ctor_set(x_95, 5, x_77);
lean_ctor_set_uint8(x_95, sizeof(void*)*6, x_78);
lean_ctor_set_uint8(x_95, sizeof(void*)*6 + 1, x_79);
if (x_72 == 0)
{
lean_object* x_96; 
lean_ctor_set_uint8(x_7, sizeof(void*)*9 + 9, x_4);
x_96 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_95, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_103 = x_96;
} else {
 lean_dec_ref(x_96);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_object* x_105; 
lean_ctor_set_uint8(x_7, sizeof(void*)*9 + 9, x_93);
x_105 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_95, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_112 = x_105;
} else {
 lean_dec_ref(x_105);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_114 = lean_ctor_get(x_7, 0);
x_115 = lean_ctor_get(x_7, 1);
x_116 = lean_ctor_get(x_7, 2);
x_117 = lean_ctor_get_uint8(x_7, sizeof(void*)*9);
x_118 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 1);
x_119 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 2);
x_120 = lean_ctor_get(x_7, 3);
x_121 = lean_ctor_get(x_7, 4);
x_122 = lean_ctor_get(x_7, 5);
x_123 = lean_ctor_get(x_7, 6);
x_124 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 3);
x_125 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 4);
x_126 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 5);
x_127 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 6);
x_128 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 7);
x_129 = lean_ctor_get(x_7, 7);
x_130 = lean_ctor_get(x_7, 8);
x_131 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 8);
x_132 = lean_ctor_get_uint8(x_7, sizeof(void*)*9 + 9);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_7);
x_133 = lean_ctor_get(x_9, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_9, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_9, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_9, 4);
lean_inc(x_136);
x_137 = lean_ctor_get(x_9, 5);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_9, sizeof(void*)*6);
x_139 = lean_ctor_get_uint8(x_9, sizeof(void*)*6 + 1);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 x_140 = x_9;
} else {
 lean_dec_ref(x_9);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get_uint8(x_15, 0);
x_142 = lean_ctor_get_uint8(x_15, 1);
x_143 = lean_ctor_get_uint8(x_15, 2);
x_144 = lean_ctor_get_uint8(x_15, 3);
x_145 = lean_ctor_get_uint8(x_15, 4);
x_146 = lean_ctor_get_uint8(x_15, 5);
x_147 = lean_ctor_get_uint8(x_15, 6);
x_148 = lean_ctor_get_uint8(x_15, 8);
x_149 = lean_ctor_get_uint8(x_15, 9);
x_150 = lean_ctor_get_uint8(x_15, 10);
x_151 = lean_ctor_get_uint8(x_15, 11);
x_152 = lean_ctor_get_uint8(x_15, 12);
if (lean_is_exclusive(x_15)) {
 x_153 = x_15;
} else {
 lean_dec_ref(x_15);
 x_153 = lean_box(0);
}
x_154 = 1;
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 0, 13);
} else {
 x_155 = x_153;
}
lean_ctor_set_uint8(x_155, 0, x_141);
lean_ctor_set_uint8(x_155, 1, x_142);
lean_ctor_set_uint8(x_155, 2, x_143);
lean_ctor_set_uint8(x_155, 3, x_144);
lean_ctor_set_uint8(x_155, 4, x_145);
lean_ctor_set_uint8(x_155, 5, x_146);
lean_ctor_set_uint8(x_155, 6, x_147);
lean_ctor_set_uint8(x_155, 7, x_154);
lean_ctor_set_uint8(x_155, 8, x_148);
lean_ctor_set_uint8(x_155, 9, x_149);
lean_ctor_set_uint8(x_155, 10, x_150);
lean_ctor_set_uint8(x_155, 11, x_151);
lean_ctor_set_uint8(x_155, 12, x_152);
if (lean_is_scalar(x_140)) {
 x_156 = lean_alloc_ctor(0, 6, 2);
} else {
 x_156 = x_140;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_133);
lean_ctor_set(x_156, 2, x_134);
lean_ctor_set(x_156, 3, x_135);
lean_ctor_set(x_156, 4, x_136);
lean_ctor_set(x_156, 5, x_137);
lean_ctor_set_uint8(x_156, sizeof(void*)*6, x_138);
lean_ctor_set_uint8(x_156, sizeof(void*)*6 + 1, x_139);
if (x_132 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_157, 0, x_114);
lean_ctor_set(x_157, 1, x_115);
lean_ctor_set(x_157, 2, x_116);
lean_ctor_set(x_157, 3, x_120);
lean_ctor_set(x_157, 4, x_121);
lean_ctor_set(x_157, 5, x_122);
lean_ctor_set(x_157, 6, x_123);
lean_ctor_set(x_157, 7, x_129);
lean_ctor_set(x_157, 8, x_130);
lean_ctor_set_uint8(x_157, sizeof(void*)*9, x_117);
lean_ctor_set_uint8(x_157, sizeof(void*)*9 + 1, x_118);
lean_ctor_set_uint8(x_157, sizeof(void*)*9 + 2, x_119);
lean_ctor_set_uint8(x_157, sizeof(void*)*9 + 3, x_124);
lean_ctor_set_uint8(x_157, sizeof(void*)*9 + 4, x_125);
lean_ctor_set_uint8(x_157, sizeof(void*)*9 + 5, x_126);
lean_ctor_set_uint8(x_157, sizeof(void*)*9 + 6, x_127);
lean_ctor_set_uint8(x_157, sizeof(void*)*9 + 7, x_128);
lean_ctor_set_uint8(x_157, sizeof(void*)*9 + 8, x_131);
lean_ctor_set_uint8(x_157, sizeof(void*)*9 + 9, x_4);
x_158 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_157, x_8, x_156, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_158, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_158, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_165 = x_158;
} else {
 lean_dec_ref(x_158);
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
x_167 = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(x_167, 0, x_114);
lean_ctor_set(x_167, 1, x_115);
lean_ctor_set(x_167, 2, x_116);
lean_ctor_set(x_167, 3, x_120);
lean_ctor_set(x_167, 4, x_121);
lean_ctor_set(x_167, 5, x_122);
lean_ctor_set(x_167, 6, x_123);
lean_ctor_set(x_167, 7, x_129);
lean_ctor_set(x_167, 8, x_130);
lean_ctor_set_uint8(x_167, sizeof(void*)*9, x_117);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 1, x_118);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 2, x_119);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 3, x_124);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 4, x_125);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 5, x_126);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 6, x_127);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 7, x_128);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 8, x_131);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 9, x_154);
x_168 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom_go(x_1, x_2, x_3, x_4, x_5, x_6, x_167, x_8, x_156, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
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
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_168, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_168, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_175 = x_168;
} else {
 lean_dec_ref(x_168);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
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
lean_dec(x_4);
x_15 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_getMainTag(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermEnsuringType___boxed), 12, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_19);
x_21 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(x_20, x_16, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermEnsuringType___boxed), 12, 3);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_28);
x_30 = l_Lean_Elab_Tactic_withCollectingNewGoalsFrom(x_29, x_26, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermWithHoles___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Elab_Tactic_elabTermWithHoles(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Tactic_refineCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_st_ref_take(x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_14, 7);
x_20 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_19, x_1, x_2);
lean_ctor_set(x_14, 7, x_20);
x_21 = lean_st_ref_set(x_8, x_13, x_15);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
x_30 = lean_ctor_get(x_14, 2);
x_31 = lean_ctor_get(x_14, 3);
x_32 = lean_ctor_get(x_14, 4);
x_33 = lean_ctor_get(x_14, 5);
x_34 = lean_ctor_get(x_14, 6);
x_35 = lean_ctor_get(x_14, 7);
x_36 = lean_ctor_get(x_14, 8);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_37 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_35, x_1, x_2);
x_38 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 3, x_31);
lean_ctor_set(x_38, 4, x_32);
lean_ctor_set(x_38, 5, x_33);
lean_ctor_set(x_38, 6, x_34);
lean_ctor_set(x_38, 7, x_37);
lean_ctor_set(x_38, 8, x_36);
lean_ctor_set(x_13, 0, x_38);
x_39 = lean_st_ref_set(x_8, x_13, x_15);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_44 = lean_ctor_get(x_13, 1);
x_45 = lean_ctor_get(x_13, 2);
x_46 = lean_ctor_get(x_13, 3);
x_47 = lean_ctor_get(x_13, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_48 = lean_ctor_get(x_14, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_14, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_14, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_14, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_14, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_14, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_14, 7);
lean_inc(x_55);
x_56 = lean_ctor_get(x_14, 8);
lean_inc(x_56);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 lean_ctor_release(x_14, 6);
 lean_ctor_release(x_14, 7);
 lean_ctor_release(x_14, 8);
 x_57 = x_14;
} else {
 lean_dec_ref(x_14);
 x_57 = lean_box(0);
}
x_58 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_55, x_1, x_2);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 9, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_49);
lean_ctor_set(x_59, 2, x_50);
lean_ctor_set(x_59, 3, x_51);
lean_ctor_set(x_59, 4, x_52);
lean_ctor_set(x_59, 5, x_53);
lean_ctor_set(x_59, 6, x_54);
lean_ctor_set(x_59, 7, x_58);
lean_ctor_set(x_59, 8, x_56);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_44);
lean_ctor_set(x_60, 2, x_45);
lean_ctor_set(x_60, 3, x_46);
lean_ctor_set(x_60, 4, x_47);
x_61 = lean_st_ref_set(x_8, x_60, x_15);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_MVarId_assign___at_Lean_Elab_Tactic_refineCore___spec__1(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Elab_Tactic_replaceMainGoal(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_16;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_refineCore___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'refine' tactic failed, value", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ndepends on the main goal metavariable '", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Tactic_elabTermWithHoles(x_1, x_16, x_2, x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_25);
x_31 = l_Lean_Expr_mvar___override(x_25);
x_32 = lean_expr_eqv(x_29, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_inc(x_25);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lambda__2___boxed), 2, 1);
lean_closure_set(x_33, 0, x_25);
lean_inc(x_29);
x_34 = l_Lean_FindMVar_main(x_33, x_29, x_17);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_free_object(x_27);
lean_free_object(x_19);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Tactic_refineCore___lambda__1(x_25, x_29, x_23, x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_23);
x_37 = l_Lean_indentExpr(x_29);
x_38 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__2;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_37);
lean_ctor_set(x_27, 0, x_38);
x_39 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__4;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_39);
lean_ctor_set(x_19, 0, x_27);
x_40 = l_Lean_MessageData_ofExpr(x_31);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_19);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__6;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_31);
lean_dec(x_29);
lean_free_object(x_19);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 0, x_25);
x_49 = l_Lean_Elab_Tactic_replaceMainGoal(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
lean_inc(x_25);
x_52 = l_Lean_Expr_mvar___override(x_25);
x_53 = lean_expr_eqv(x_50, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_inc(x_25);
x_54 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lambda__2___boxed), 2, 1);
lean_closure_set(x_54, 0, x_25);
lean_inc(x_50);
x_55 = l_Lean_FindMVar_main(x_54, x_50, x_17);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_52);
lean_free_object(x_19);
x_56 = lean_box(0);
x_57 = l_Lean_Elab_Tactic_refineCore___lambda__1(x_25, x_50, x_23, x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_55);
lean_dec(x_25);
lean_dec(x_23);
x_58 = l_Lean_indentExpr(x_50);
x_59 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__2;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__4;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_61);
lean_ctor_set(x_19, 0, x_60);
x_62 = l_Lean_MessageData_ofExpr(x_52);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_19);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__6;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_52);
lean_dec(x_50);
lean_free_object(x_19);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_25);
lean_ctor_set(x_71, 1, x_23);
x_72 = l_Lean_Elab_Tactic_replaceMainGoal(x_71, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_free_object(x_19);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_24);
if (x_73 == 0)
{
return x_24;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_24, 0);
x_75 = lean_ctor_get(x_24, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_24);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_19, 0);
x_78 = lean_ctor_get(x_19, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_19);
x_79 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_77, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_81);
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
lean_inc(x_80);
x_86 = l_Lean_Expr_mvar___override(x_80);
x_87 = lean_expr_eqv(x_83, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_inc(x_80);
x_88 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lambda__2___boxed), 2, 1);
lean_closure_set(x_88, 0, x_80);
lean_inc(x_83);
x_89 = l_Lean_FindMVar_main(x_88, x_83, x_17);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_86);
lean_dec(x_85);
x_90 = lean_box(0);
x_91 = l_Lean_Elab_Tactic_refineCore___lambda__1(x_80, x_83, x_78, x_90, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_84);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_89);
lean_dec(x_80);
lean_dec(x_78);
x_92 = l_Lean_indentExpr(x_83);
x_93 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__2;
if (lean_is_scalar(x_85)) {
 x_94 = lean_alloc_ctor(7, 2, 0);
} else {
 x_94 = x_85;
 lean_ctor_set_tag(x_94, 7);
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__4;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_MessageData_ofExpr(x_86);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__6;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_100, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_84);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_86);
lean_dec(x_83);
if (lean_is_scalar(x_85)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_85;
 lean_ctor_set_tag(x_106, 1);
}
lean_ctor_set(x_106, 0, x_80);
lean_ctor_set(x_106, 1, x_78);
x_107 = l_Lean_Elab_Tactic_replaceMainGoal(x_106, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_84);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_108 = lean_ctor_get(x_79, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_79, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_110 = x_79;
} else {
 lean_dec_ref(x_79);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = !lean_is_exclusive(x_18);
if (x_112 == 0)
{
return x_18;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_18, 0);
x_114 = lean_ctor_get(x_18, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_18);
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
x_116 = !lean_is_exclusive(x_13);
if (x_116 == 0)
{
return x_13;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_13, 0);
x_118 = lean_ctor_get(x_13, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_13);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_refineCore___lambda__3___boxed), 12, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_13);
x_15 = l_Lean_Elab_Tactic_withMainContext___rarg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Tactic_refineCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_assign___at_Lean_Elab_Tactic_refineCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_refineCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Tactic_refineCore___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_Tactic_refineCore___lambda__3(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_refineCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_Tactic_refineCore(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refine", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l_Lean_Elab_Tactic_evalRefine___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalRefine___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalRefine___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Elab_Tactic_evalRefine___closed__3;
x_17 = 0;
x_18 = l_Lean_Elab_Tactic_refineCore(x_15, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalRefine", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalRefine___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(189u);
x_2 = lean_unsigned_to_nat(27u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(192u);
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(27u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(50u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(189u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(189u);
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(31u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(41u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refine'", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l_Lean_Elab_Tactic_evalRefine_x27___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalRefine_x27___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRefine_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalRefine_x27___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Elab_Tactic_evalRefine_x27___closed__3;
x_17 = 1;
x_18 = l_Lean_Elab_Tactic_refineCore(x_15, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalRefine'", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRefine_x27), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalRefine_x27___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(194u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(197u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(51u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(194u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(194u);
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(43u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'specialize' requires a term of the form `h x_1 .. x_n` where `h` appears in the local context", 94, 94);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_14 = l_Lean_Elab_Tactic_elabTermWithHoles(x_1, x_2, x_3, x_13, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Expr_getAppFn(x_17);
x_20 = l_Lean_Expr_isFVar(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_21 = l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__2;
x_22 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Expr_fvarId_x21(x_19);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_23);
x_24 = l_Lean_FVarId_getDecl(x_23, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_17);
x_30 = lean_infer_type(x_17, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_LocalDecl_userName(x_25);
lean_dec(x_25);
x_34 = l_Lean_Expr_headBeta(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_35 = l_Lean_MVarId_assert(x_28, x_33, x_34, x_17, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_38 = l_Lean_Meta_intro1Core(x_36, x_13, x_8, x_9, x_10, x_11, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_44 = l_Lean_MVarId_tryClear(x_42, x_23, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 1, x_47);
lean_ctor_set(x_39, 0, x_45);
x_48 = l_List_appendTR___rarg(x_18, x_39);
x_49 = l_Lean_Elab_Tactic_replaceMainGoal(x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_49;
}
else
{
uint8_t x_50; 
lean_free_object(x_39);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
return x_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_44);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_dec(x_39);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_55 = l_Lean_MVarId_tryClear(x_54, x_23, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_List_appendTR___rarg(x_18, x_59);
x_61 = l_Lean_Elab_Tactic_replaceMainGoal(x_60, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_64 = x_55;
} else {
 lean_dec_ref(x_55);
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
else
{
uint8_t x_66; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_38);
if (x_66 == 0)
{
return x_38;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_38, 0);
x_68 = lean_ctor_get(x_38, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_38);
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
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_35);
if (x_70 == 0)
{
return x_35;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_35, 0);
x_72 = lean_ctor_get(x_35, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_35);
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
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_30);
if (x_74 == 0)
{
return x_30;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_30, 0);
x_76 = lean_ctor_get(x_30, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_30);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_82; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_24);
if (x_82 == 0)
{
return x_24;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_24, 0);
x_84 = lean_ctor_get(x_24, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_24);
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
uint8_t x_86; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_14);
if (x_86 == 0)
{
return x_14;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_14, 0);
x_88 = lean_ctor_get(x_14, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_14);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("specialize", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSpecialize___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSpecialize___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalSpecialize___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSpecialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalSpecialize___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_evalSpecialize___closed__3;
x_14 = l_Lean_Elab_Tactic_withMainContext___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Tactic_evalSpecialize___closed__4;
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize___lambda__1), 12, 3);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
x_20 = l_Lean_Elab_Tactic_withMainContext___rarg(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSpecialize", 14, 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSpecialize), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalSpecialize___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(199u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(212u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(31u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__2;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(199u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(199u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(35u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(49u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Tactic_elabTerm(x_1, x_13, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabTermForApply___closed__1() {
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
uint8_t x_12; 
x_12 = l_Lean_Syntax_isIdent(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Tactic_elabTermForApply___lambda__1(x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = l_Lean_Elab_Tactic_elabTermForApply___closed__1;
x_16 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_17 = l_Lean_Elab_Term_resolveId_x3f(x_1, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Tactic_elabTermForApply___lambda__1(x_1, x_2, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Tactic_elabTermForApply___lambda__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabTermForApply___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_elabTermForApply(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
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
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected term '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'; expected single reference to variable", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getFVarId___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_inc(x_2);
x_11 = l_Lean_Elab_Tactic_withoutRecover___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_11);
x_20 = l_Lean_MessageData_ofExpr(x_12);
x_21 = l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
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
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = 0;
x_12 = lean_box(x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTermForApply___boxed), 11, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId___lambda__1), 10, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 5);
x_17 = l_Lean_replaceRef(x_1, x_16);
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_8, 5, x_17);
x_18 = l_Lean_Elab_Tactic_withMainContext___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_30 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_31 = lean_ctor_get(x_8, 11);
x_32 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
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
x_33 = l_Lean_replaceRef(x_1, x_24);
lean_dec(x_24);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_20);
lean_ctor_set(x_34, 2, x_21);
lean_ctor_set(x_34, 3, x_22);
lean_ctor_set(x_34, 4, x_23);
lean_ctor_set(x_34, 5, x_33);
lean_ctor_set(x_34, 6, x_25);
lean_ctor_set(x_34, 7, x_26);
lean_ctor_set(x_34, 8, x_27);
lean_ctor_set(x_34, 9, x_28);
lean_ctor_set(x_34, 10, x_29);
lean_ctor_set(x_34, 11, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*12, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*12 + 1, x_32);
x_35 = l_Lean_Elab_Tactic_withMainContext___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_34, x_9, x_10);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_2, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_uget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Tactic_getFVarId(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_17, x_2, x_19);
x_2 = x_22;
x_3 = x_23;
x_12 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
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
x_14 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1___boxed), 12, 3);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_1);
x_15 = l_Lean_Elab_Tactic_withMainContext___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = lean_apply_7(x_1, x_14, x_2, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_19, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Tactic_replaceMainGoal(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_Tactic_elabTermForApply(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_isMVar(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Tactic_evalApplyLikeTactic___lambda__1(x_2, x_17, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = 1;
x_23 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_22, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Tactic_evalApplyLikeTactic___lambda__1(x_2, x_27, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_4);
lean_dec(x_3);
return x_30;
}
else
{
uint8_t x_31; 
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
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApplyLikeTactic___lambda__2), 11, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
x_13 = l_Lean_Elab_Tactic_withMainContext___rarg(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApplyLikeTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalApplyLikeTactic___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_Tactic_evalApply___lambda__1___closed__1;
x_9 = l_Lean_MVarId_apply(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("apply", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l_Lean_Elab_Tactic_evalApply___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalApply___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply___lambda__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalApply(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalApply___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Elab_Tactic_evalApply___closed__3;
x_17 = l_Lean_Elab_Tactic_evalApplyLikeTactic(x_16, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalApply", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalApply), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalApply___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(303u);
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(306u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(43u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(303u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(303u);
x_2 = lean_unsigned_to_nat(56u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(47u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(56u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_evalApply___lambda__1___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_MVarId_constructor(x_11, x_13, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_Tactic_replaceMainGoal(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
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
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalConstructor___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalConstructor___rarg___lambda__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_evalConstructor___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalConstructor___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalConstructor___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalConstructor___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalConstructor(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("constructor", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalConstructor", 15, 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalConstructor___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(308u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(312u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(49u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(28u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(308u);
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(308u);
x_2 = lean_unsigned_to_nat(68u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(53u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(68u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 2;
lean_ctor_set_uint8(x_14, 9, x_16);
x_17 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
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
uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get_uint8(x_14, 0);
x_27 = lean_ctor_get_uint8(x_14, 1);
x_28 = lean_ctor_get_uint8(x_14, 2);
x_29 = lean_ctor_get_uint8(x_14, 3);
x_30 = lean_ctor_get_uint8(x_14, 4);
x_31 = lean_ctor_get_uint8(x_14, 5);
x_32 = lean_ctor_get_uint8(x_14, 6);
x_33 = lean_ctor_get_uint8(x_14, 7);
x_34 = lean_ctor_get_uint8(x_14, 8);
x_35 = lean_ctor_get_uint8(x_14, 10);
x_36 = lean_ctor_get_uint8(x_14, 11);
x_37 = lean_ctor_get_uint8(x_14, 12);
lean_dec(x_14);
x_38 = 2;
x_39 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_39, 0, x_26);
lean_ctor_set_uint8(x_39, 1, x_27);
lean_ctor_set_uint8(x_39, 2, x_28);
lean_ctor_set_uint8(x_39, 3, x_29);
lean_ctor_set_uint8(x_39, 4, x_30);
lean_ctor_set_uint8(x_39, 5, x_31);
lean_ctor_set_uint8(x_39, 6, x_32);
lean_ctor_set_uint8(x_39, 7, x_33);
lean_ctor_set_uint8(x_39, 8, x_34);
lean_ctor_set_uint8(x_39, 9, x_38);
lean_ctor_set_uint8(x_39, 10, x_35);
lean_ctor_set_uint8(x_39, 11, x_36);
lean_ctor_set_uint8(x_39, 12, x_37);
lean_ctor_set(x_6, 0, x_39);
x_40 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get(x_6, 1);
x_51 = lean_ctor_get(x_6, 2);
x_52 = lean_ctor_get(x_6, 3);
x_53 = lean_ctor_get(x_6, 4);
x_54 = lean_ctor_get(x_6, 5);
x_55 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_56 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_6);
x_57 = lean_ctor_get_uint8(x_49, 0);
x_58 = lean_ctor_get_uint8(x_49, 1);
x_59 = lean_ctor_get_uint8(x_49, 2);
x_60 = lean_ctor_get_uint8(x_49, 3);
x_61 = lean_ctor_get_uint8(x_49, 4);
x_62 = lean_ctor_get_uint8(x_49, 5);
x_63 = lean_ctor_get_uint8(x_49, 6);
x_64 = lean_ctor_get_uint8(x_49, 7);
x_65 = lean_ctor_get_uint8(x_49, 8);
x_66 = lean_ctor_get_uint8(x_49, 10);
x_67 = lean_ctor_get_uint8(x_49, 11);
x_68 = lean_ctor_get_uint8(x_49, 12);
if (lean_is_exclusive(x_49)) {
 x_69 = x_49;
} else {
 lean_dec_ref(x_49);
 x_69 = lean_box(0);
}
x_70 = 2;
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 0, 13);
} else {
 x_71 = x_69;
}
lean_ctor_set_uint8(x_71, 0, x_57);
lean_ctor_set_uint8(x_71, 1, x_58);
lean_ctor_set_uint8(x_71, 2, x_59);
lean_ctor_set_uint8(x_71, 3, x_60);
lean_ctor_set_uint8(x_71, 4, x_61);
lean_ctor_set_uint8(x_71, 5, x_62);
lean_ctor_set_uint8(x_71, 6, x_63);
lean_ctor_set_uint8(x_71, 7, x_64);
lean_ctor_set_uint8(x_71, 8, x_65);
lean_ctor_set_uint8(x_71, 9, x_70);
lean_ctor_set_uint8(x_71, 10, x_66);
lean_ctor_set_uint8(x_71, 11, x_67);
lean_ctor_set_uint8(x_71, 12, x_68);
x_72 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_50);
lean_ctor_set(x_72, 2, x_51);
lean_ctor_set(x_72, 3, x_52);
lean_ctor_set(x_72, 4, x_53);
lean_ctor_set(x_72, 5, x_54);
lean_ctor_set_uint8(x_72, sizeof(void*)*6, x_55);
lean_ctor_set_uint8(x_72, sizeof(void*)*6 + 1, x_56);
x_73 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_72, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withReducible", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalWithReducible", 17, 17);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducible___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(314u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(315u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(51u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(36u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(314u);
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(314u);
x_2 = lean_unsigned_to_nat(72u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(55u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(72u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithReducibleAndInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 3;
lean_ctor_set_uint8(x_14, 9, x_16);
x_17 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
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
uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get_uint8(x_14, 0);
x_27 = lean_ctor_get_uint8(x_14, 1);
x_28 = lean_ctor_get_uint8(x_14, 2);
x_29 = lean_ctor_get_uint8(x_14, 3);
x_30 = lean_ctor_get_uint8(x_14, 4);
x_31 = lean_ctor_get_uint8(x_14, 5);
x_32 = lean_ctor_get_uint8(x_14, 6);
x_33 = lean_ctor_get_uint8(x_14, 7);
x_34 = lean_ctor_get_uint8(x_14, 8);
x_35 = lean_ctor_get_uint8(x_14, 10);
x_36 = lean_ctor_get_uint8(x_14, 11);
x_37 = lean_ctor_get_uint8(x_14, 12);
lean_dec(x_14);
x_38 = 3;
x_39 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_39, 0, x_26);
lean_ctor_set_uint8(x_39, 1, x_27);
lean_ctor_set_uint8(x_39, 2, x_28);
lean_ctor_set_uint8(x_39, 3, x_29);
lean_ctor_set_uint8(x_39, 4, x_30);
lean_ctor_set_uint8(x_39, 5, x_31);
lean_ctor_set_uint8(x_39, 6, x_32);
lean_ctor_set_uint8(x_39, 7, x_33);
lean_ctor_set_uint8(x_39, 8, x_34);
lean_ctor_set_uint8(x_39, 9, x_38);
lean_ctor_set_uint8(x_39, 10, x_35);
lean_ctor_set_uint8(x_39, 11, x_36);
lean_ctor_set_uint8(x_39, 12, x_37);
lean_ctor_set(x_6, 0, x_39);
x_40 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get(x_6, 1);
x_51 = lean_ctor_get(x_6, 2);
x_52 = lean_ctor_get(x_6, 3);
x_53 = lean_ctor_get(x_6, 4);
x_54 = lean_ctor_get(x_6, 5);
x_55 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_56 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_6);
x_57 = lean_ctor_get_uint8(x_49, 0);
x_58 = lean_ctor_get_uint8(x_49, 1);
x_59 = lean_ctor_get_uint8(x_49, 2);
x_60 = lean_ctor_get_uint8(x_49, 3);
x_61 = lean_ctor_get_uint8(x_49, 4);
x_62 = lean_ctor_get_uint8(x_49, 5);
x_63 = lean_ctor_get_uint8(x_49, 6);
x_64 = lean_ctor_get_uint8(x_49, 7);
x_65 = lean_ctor_get_uint8(x_49, 8);
x_66 = lean_ctor_get_uint8(x_49, 10);
x_67 = lean_ctor_get_uint8(x_49, 11);
x_68 = lean_ctor_get_uint8(x_49, 12);
if (lean_is_exclusive(x_49)) {
 x_69 = x_49;
} else {
 lean_dec_ref(x_49);
 x_69 = lean_box(0);
}
x_70 = 3;
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 0, 13);
} else {
 x_71 = x_69;
}
lean_ctor_set_uint8(x_71, 0, x_57);
lean_ctor_set_uint8(x_71, 1, x_58);
lean_ctor_set_uint8(x_71, 2, x_59);
lean_ctor_set_uint8(x_71, 3, x_60);
lean_ctor_set_uint8(x_71, 4, x_61);
lean_ctor_set_uint8(x_71, 5, x_62);
lean_ctor_set_uint8(x_71, 6, x_63);
lean_ctor_set_uint8(x_71, 7, x_64);
lean_ctor_set_uint8(x_71, 8, x_65);
lean_ctor_set_uint8(x_71, 9, x_70);
lean_ctor_set_uint8(x_71, 10, x_66);
lean_ctor_set_uint8(x_71, 11, x_67);
lean_ctor_set_uint8(x_71, 12, x_68);
x_72 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_50);
lean_ctor_set(x_72, 2, x_51);
lean_ctor_set(x_72, 3, x_52);
lean_ctor_set(x_72, 4, x_53);
lean_ctor_set(x_72, 5, x_54);
lean_ctor_set_uint8(x_72, sizeof(void*)*6, x_55);
lean_ctor_set_uint8(x_72, sizeof(void*)*6 + 1, x_56);
x_73 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_72, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withReducibleAndInstances", 25, 25);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalWithReducibleAndInstances", 29, 29);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithReducibleAndInstances___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(317u);
x_2 = lean_unsigned_to_nat(63u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(318u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(63u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(48u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(317u);
x_2 = lean_unsigned_to_nat(67u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(317u);
x_2 = lean_unsigned_to_nat(96u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(67u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(96u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalWithUnfoldingAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
lean_ctor_set_uint8(x_14, 9, x_16);
x_17 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
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
uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get_uint8(x_14, 0);
x_27 = lean_ctor_get_uint8(x_14, 1);
x_28 = lean_ctor_get_uint8(x_14, 2);
x_29 = lean_ctor_get_uint8(x_14, 3);
x_30 = lean_ctor_get_uint8(x_14, 4);
x_31 = lean_ctor_get_uint8(x_14, 5);
x_32 = lean_ctor_get_uint8(x_14, 6);
x_33 = lean_ctor_get_uint8(x_14, 7);
x_34 = lean_ctor_get_uint8(x_14, 8);
x_35 = lean_ctor_get_uint8(x_14, 10);
x_36 = lean_ctor_get_uint8(x_14, 11);
x_37 = lean_ctor_get_uint8(x_14, 12);
lean_dec(x_14);
x_38 = 0;
x_39 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_39, 0, x_26);
lean_ctor_set_uint8(x_39, 1, x_27);
lean_ctor_set_uint8(x_39, 2, x_28);
lean_ctor_set_uint8(x_39, 3, x_29);
lean_ctor_set_uint8(x_39, 4, x_30);
lean_ctor_set_uint8(x_39, 5, x_31);
lean_ctor_set_uint8(x_39, 6, x_32);
lean_ctor_set_uint8(x_39, 7, x_33);
lean_ctor_set_uint8(x_39, 8, x_34);
lean_ctor_set_uint8(x_39, 9, x_38);
lean_ctor_set_uint8(x_39, 10, x_35);
lean_ctor_set_uint8(x_39, 11, x_36);
lean_ctor_set_uint8(x_39, 12, x_37);
lean_ctor_set(x_6, 0, x_39);
x_40 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get(x_6, 1);
x_51 = lean_ctor_get(x_6, 2);
x_52 = lean_ctor_get(x_6, 3);
x_53 = lean_ctor_get(x_6, 4);
x_54 = lean_ctor_get(x_6, 5);
x_55 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
x_56 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_6);
x_57 = lean_ctor_get_uint8(x_49, 0);
x_58 = lean_ctor_get_uint8(x_49, 1);
x_59 = lean_ctor_get_uint8(x_49, 2);
x_60 = lean_ctor_get_uint8(x_49, 3);
x_61 = lean_ctor_get_uint8(x_49, 4);
x_62 = lean_ctor_get_uint8(x_49, 5);
x_63 = lean_ctor_get_uint8(x_49, 6);
x_64 = lean_ctor_get_uint8(x_49, 7);
x_65 = lean_ctor_get_uint8(x_49, 8);
x_66 = lean_ctor_get_uint8(x_49, 10);
x_67 = lean_ctor_get_uint8(x_49, 11);
x_68 = lean_ctor_get_uint8(x_49, 12);
if (lean_is_exclusive(x_49)) {
 x_69 = x_49;
} else {
 lean_dec_ref(x_49);
 x_69 = lean_box(0);
}
x_70 = 0;
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 0, 13);
} else {
 x_71 = x_69;
}
lean_ctor_set_uint8(x_71, 0, x_57);
lean_ctor_set_uint8(x_71, 1, x_58);
lean_ctor_set_uint8(x_71, 2, x_59);
lean_ctor_set_uint8(x_71, 3, x_60);
lean_ctor_set_uint8(x_71, 4, x_61);
lean_ctor_set_uint8(x_71, 5, x_62);
lean_ctor_set_uint8(x_71, 6, x_63);
lean_ctor_set_uint8(x_71, 7, x_64);
lean_ctor_set_uint8(x_71, 8, x_65);
lean_ctor_set_uint8(x_71, 9, x_70);
lean_ctor_set_uint8(x_71, 10, x_66);
lean_ctor_set_uint8(x_71, 11, x_67);
lean_ctor_set_uint8(x_71, 12, x_68);
x_72 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_50);
lean_ctor_set(x_72, 2, x_51);
lean_ctor_set(x_72, 3, x_52);
lean_ctor_set(x_72, 4, x_53);
lean_ctor_set(x_72, 5, x_54);
lean_ctor_set_uint8(x_72, sizeof(void*)*6, x_55);
lean_ctor_set_uint8(x_72, sizeof(void*)*6 + 1, x_56);
x_73 = l_Lean_Elab_Tactic_evalTactic(x_12, x_2, x_3, x_4, x_5, x_72, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_80 = x_73;
} else {
 lean_dec_ref(x_73);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withUnfoldingAll", 16, 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalWithUnfoldingAll", 20, 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalWithUnfoldingAll___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(320u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(321u);
x_2 = lean_unsigned_to_nat(60u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(54u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(60u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(320u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(320u);
x_2 = lean_unsigned_to_nat(78u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(58u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(78u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_15);
x_23 = lean_infer_type(x_15, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_MVarId_assert(x_27, x_29, x_24, x_15, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Meta_intro1Core(x_31, x_13, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
x_39 = lean_box(0);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 1, x_39);
lean_ctor_set(x_34, 0, x_38);
x_40 = l_Lean_Elab_Tactic_replaceMainGoal(x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_37);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_37);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_34, 0);
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_34);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Tactic_replaceMainGoal(x_52, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_49);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
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
else
{
uint8_t x_61; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_33);
if (x_61 == 0)
{
return x_33;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_33, 0);
x_63 = lean_ctor_get(x_33, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_33);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_30);
if (x_65 == 0)
{
return x_30;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_30, 0);
x_67 = lean_ctor_get(x_30, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_30);
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
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_26);
if (x_69 == 0)
{
return x_26;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_26, 0);
x_71 = lean_ctor_get(x_26, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_26);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_23, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_23, 1);
lean_inc(x_74);
lean_dec(x_23);
x_75 = lean_ctor_get(x_3, 0);
lean_inc(x_75);
lean_dec(x_3);
x_76 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_79 = l_Lean_MVarId_assert(x_77, x_75, x_73, x_15, x_8, x_9, x_10, x_11, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_83 = l_Lean_Meta_intro1Core(x_80, x_82, x_8, x_9, x_10, x_11, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_84, 0);
x_88 = lean_ctor_get(x_84, 1);
x_89 = lean_box(0);
lean_ctor_set_tag(x_84, 1);
lean_ctor_set(x_84, 1, x_89);
lean_ctor_set(x_84, 0, x_88);
x_90 = l_Lean_Elab_Tactic_replaceMainGoal(x_84, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_85);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
lean_ctor_set(x_90, 0, x_87);
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_87);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_87);
x_95 = !lean_is_exclusive(x_90);
if (x_95 == 0)
{
return x_90;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_90, 0);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_90);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_84, 0);
x_100 = lean_ctor_get(x_84, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_84);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Elab_Tactic_replaceMainGoal(x_102, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_85);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
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
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_99);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_111 = !lean_is_exclusive(x_83);
if (x_111 == 0)
{
return x_83;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_83, 0);
x_113 = lean_ctor_get(x_83, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_83);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_115 = !lean_is_exclusive(x_79);
if (x_115 == 0)
{
return x_79;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_79, 0);
x_117 = lean_ctor_get(x_79, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_79);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_119 = !lean_is_exclusive(x_76);
if (x_119 == 0)
{
return x_76;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_76, 0);
x_121 = lean_ctor_get(x_76, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_76);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_23);
if (x_123 == 0)
{
return x_23;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_23, 0);
x_125 = lean_ctor_get(x_23, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_23);
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
uint8_t x_127; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_127 = !lean_is_exclusive(x_14);
if (x_127 == 0)
{
return x_14;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_14, 0);
x_129 = lean_ctor_get(x_14, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_14);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsFVar___lambda__1), 12, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_2);
x_14 = l_Lean_Elab_Tactic_withMainContext___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_18 = lean_array_fget(x_2, x_17);
if (lean_obj_tag(x_18) == 0)
{
x_3 = x_17;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = l_Lean_LocalDecl_type(x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_23 = l_Lean_Meta_isExprDefEq(x_1, x_22, x_9, x_10, x_11, x_12, x_13);
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
lean_free_object(x_18);
lean_dec(x_21);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_3 = x_17;
x_4 = lean_box(0);
x_13 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = l_Lean_LocalDecl_fvarId(x_21);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_30);
lean_ctor_set(x_23, 0, x_18);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = l_Lean_LocalDecl_fvarId(x_21);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
lean_dec(x_18);
x_39 = l_Lean_LocalDecl_type(x_38);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_40 = l_Lean_Meta_isExprDefEq(x_1, x_39, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_38);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_3 = x_17;
x_4 = lean_box(0);
x_13 = x_43;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
x_47 = l_Lean_LocalDecl_fvarId(x_38);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_38);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_52 = x_40;
} else {
 lean_dec_ref(x_40);
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
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_13);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_18 = lean_array_fget(x_2, x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_19 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Elab_Tactic_evalRename___spec__4(x_1, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_3 = x_17;
x_4 = lean_box(0);
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_13);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_18 = lean_array_fget(x_2, x_17);
if (lean_obj_tag(x_18) == 0)
{
x_3 = x_17;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = l_Lean_LocalDecl_type(x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_23 = l_Lean_Meta_isExprDefEq(x_1, x_22, x_9, x_10, x_11, x_12, x_13);
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
lean_free_object(x_18);
lean_dec(x_21);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_3 = x_17;
x_4 = lean_box(0);
x_13 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = l_Lean_LocalDecl_fvarId(x_21);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_30);
lean_ctor_set(x_23, 0, x_18);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = l_Lean_LocalDecl_fvarId(x_21);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_18);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
lean_dec(x_18);
x_39 = l_Lean_LocalDecl_type(x_38);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_40 = l_Lean_Meta_isExprDefEq(x_1, x_39, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_38);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_3 = x_17;
x_4 = lean_box(0);
x_13 = x_43;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
x_47 = l_Lean_LocalDecl_fvarId(x_38);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_38);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_52 = x_40;
} else {
 lean_dec_ref(x_40);
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
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_13);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Elab_Tactic_evalRename___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_array_get_size(x_12);
x_14 = l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__5(x_1, x_12, x_13, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_array_get_size(x_15);
x_17 = l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__6(x_1, x_15, x_16, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_array_get_size(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_14 = l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__3(x_1, x_12, x_13, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_17 = lean_ctor_get(x_2, 0);
x_18 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Elab_Tactic_evalRename___spec__4(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__2(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_evalRename___spec__7___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_4(x_1, x_3, x_4, x_5, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(x_2, x_12, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_evalRename___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_evalRename___spec__7___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_Tactic_evalRename___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Tactic_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = l_Lean_Elab_Tactic_SavedState_restore(x_12, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = 0;
x_26 = l_Lean_Elab_Tactic_SavedState_restore(x_12, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to find a hypothesis with type", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_Tactic_elabTerm(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_17 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__1(x_14, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_16);
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
lean_dec(x_17);
x_20 = l_Lean_indentExpr(x_14);
x_21 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_10);
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
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_12 = l_Lean_withoutModifyingState___at_Lean_Elab_Tactic_evalRename___spec__8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Syntax_getId(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l_Lean_MVarId_rename(x_16, x_13, x_18, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Elab_Tactic_replaceMainGoal(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rename", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l_Lean_Elab_Tactic_evalRename___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRename___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalRename___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalRename___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = l_Lean_Elab_Tactic_evalRename___closed__4;
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_box(0);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lambda__1), 11, 2);
lean_closure_set(x_22, 0, x_15);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___rarg), 10, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_evalRename___spec__7___rarg___boxed), 11, 2);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename___lambda__2___boxed), 11, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_17);
x_28 = l_Lean_Elab_Tactic_withMainContext___rarg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_findSomeRevM_x3f_find___at_Lean_Elab_Tactic_evalRename___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Elab_Tactic_evalRename___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Elab_Tactic_evalRename___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Elab_Tactic_evalRename___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_evalRename___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Elab_Tactic_evalRename___spec__7___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalRename___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalRename___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalRename", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRename), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalRename___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(344u);
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(359u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(44u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(344u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(344u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(48u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(58u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected type must not contain free variables", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nUse the '+revert' option to automatically cleanup and revert free variables.", 77, 77);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasFVar(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = l_Lean_indentExpr(x_1);
x_13 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected type must not contain meta variables", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasMVar(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = l_Lean_indentExpr(x_1);
x_14 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_zetaReduce___lambda__2___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1;
x_13 = l_Lean_Expr_hasFVar(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_apply_9(x_12, x_10, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_16 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2;
x_17 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3;
x_18 = 1;
x_19 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_10, x_16, x_17, x_18, x_19, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_apply_9(x_12, x_21, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isTrue", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__1;
x_2 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isFalse", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__1;
x_2 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_9, x_6);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_8, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_31; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_8, x_21);
lean_dec(x_8);
x_74 = lean_ctor_get(x_1, 0);
x_75 = lean_nat_add(x_74, x_21);
x_76 = lean_nat_add(x_75, x_9);
lean_dec(x_75);
x_77 = lean_array_get_size(x_2);
x_78 = lean_nat_dec_lt(x_76, x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_76);
x_79 = l_Lean_instInhabitedExpr;
x_80 = l_outOfBounds___rarg(x_79);
x_31 = x_80;
goto block_73;
}
else
{
lean_object* x_81; 
x_81 = lean_array_fget(x_2, x_76);
lean_dec(x_76);
x_31 = x_81;
goto block_73;
}
block_30:
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_8 = x_22;
x_9 = x_28;
x_10 = lean_box(0);
x_11 = x_27;
x_16 = x_24;
goto _start;
}
}
block_73:
{
lean_object* x_32; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_31);
x_32 = lean_infer_type(x_31, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_35 = l_Lean_Meta_isClass_x3f(x_33, x_12, x_13, x_14, x_15, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__3;
x_39 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_IR_IRType_beq___spec__1(x_36, x_38);
lean_dec(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_31);
lean_inc(x_4);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_4);
x_23 = x_40;
x_24 = x_37;
goto block_30;
}
else
{
lean_object* x_41; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_41 = lean_whnf(x_31, x_12, x_13, x_14, x_15, x_37);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5;
x_45 = l_Lean_Expr_isAppOf(x_42, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__7;
x_47 = l_Lean_Expr_isAppOf(x_42, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_48 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_42, x_12, x_13, x_14, x_15, x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_23 = x_54;
x_24 = x_50;
goto block_30;
}
else
{
uint8_t x_55; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
return x_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_42);
lean_inc(x_4);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_4);
x_23 = x_59;
x_24 = x_43;
goto block_30;
}
}
else
{
lean_object* x_60; 
lean_dec(x_42);
lean_inc(x_4);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_4);
x_23 = x_60;
x_24 = x_43;
goto block_30;
}
}
else
{
uint8_t x_61; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_41);
if (x_61 == 0)
{
return x_41;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_41, 0);
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_41);
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
lean_dec(x_31);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_35);
if (x_65 == 0)
{
return x_35;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_35, 0);
x_67 = lean_ctor_get(x_35, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_35);
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
lean_dec(x_31);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_32);
if (x_69 == 0)
{
return x_32;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_32, 0);
x_71 = lean_ctor_get(x_32, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_32);
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
lean_object* x_82; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_16);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__2() {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_reduceMatcher_x3f___spec__1(x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_20);
x_22 = l_Lean_Meta_Match_MatcherInfo_arity(x_19);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_10);
x_24 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__1;
lean_inc(x_21);
x_25 = lean_mk_array(x_21, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_21, x_26);
lean_dec(x_21);
lean_inc(x_1);
x_28 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_25, x_27);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_26);
x_31 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__2;
lean_inc(x_29);
x_32 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1(x_19, x_28, x_30, x_31, x_20, x_29, x_26, x_29, x_20, lean_box(0), x_31, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_29);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_19);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
lean_ctor_set(x_32, 0, x_1);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_41);
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
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
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_dec(x_10);
x_50 = lean_ctor_get(x_11, 0);
lean_inc(x_50);
lean_dec(x_11);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_51);
x_53 = l_Lean_Meta_Match_MatcherInfo_arity(x_50);
x_54 = lean_nat_dec_eq(x_52, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__1;
lean_inc(x_52);
x_57 = lean_mk_array(x_52, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_52, x_58);
lean_dec(x_52);
lean_inc(x_1);
x_60 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_57, x_59);
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_inc(x_61);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_51);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_58);
x_63 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__2;
lean_inc(x_61);
x_64 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1(x_50, x_60, x_62, x_63, x_51, x_61, x_58, x_61, x_51, lean_box(0), x_63, x_3, x_4, x_5, x_6, x_49);
lean_dec(x_61);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_50);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
lean_dec(x_66);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_1);
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_64, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_76 = x_64;
} else {
 lean_dec_ref(x_64);
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
}
}
else
{
lean_object* x_78; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_7);
return x_78;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__1;
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 7);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 8);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 9);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 10);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*12);
x_19 = lean_ctor_get(x_4, 11);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*12 + 1);
x_21 = lean_nat_dec_eq(x_10, x_11);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_4, 11);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 10);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 9);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 8);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 7);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 6);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 5);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 4);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_4, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_10, x_35);
lean_dec(x_10);
lean_ctor_set(x_4, 3, x_36);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_37 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2;
x_41 = lean_unsigned_to_nat(5u);
x_42 = l_Lean_Expr_isAppOfArity(x_38, x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2(x_38, x_43, x_2, x_3, x_4, x_5, x_39);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Expr_appArg_x21(x_38);
lean_dec(x_38);
x_46 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_45, x_2, x_3, x_4, x_5, x_39);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
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
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
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
}
else
{
uint8_t x_55; 
lean_dec(x_4);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_37);
if (x_55 == 0)
{
return x_37;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_37, 0);
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_37);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_4);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_10, x_59);
lean_dec(x_10);
x_61 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_61, 0, x_7);
lean_ctor_set(x_61, 1, x_8);
lean_ctor_set(x_61, 2, x_9);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_11);
lean_ctor_set(x_61, 5, x_12);
lean_ctor_set(x_61, 6, x_13);
lean_ctor_set(x_61, 7, x_14);
lean_ctor_set(x_61, 8, x_15);
lean_ctor_set(x_61, 9, x_16);
lean_ctor_set(x_61, 10, x_17);
lean_ctor_set(x_61, 11, x_19);
lean_ctor_set_uint8(x_61, sizeof(void*)*12, x_18);
lean_ctor_set_uint8(x_61, sizeof(void*)*12 + 1, x_20);
lean_inc(x_5);
lean_inc(x_61);
lean_inc(x_3);
lean_inc(x_2);
x_62 = lean_whnf(x_1, x_2, x_3, x_61, x_5, x_6);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2;
x_66 = lean_unsigned_to_nat(5u);
x_67 = l_Lean_Expr_isAppOfArity(x_63, x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_box(0);
x_69 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2(x_63, x_68, x_2, x_3, x_61, x_5, x_64);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Lean_Expr_appArg_x21(x_63);
lean_dec(x_63);
x_71 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_70, x_2, x_3, x_61, x_5, x_64);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
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
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_78 = x_71;
} else {
 lean_dec_ref(x_71);
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
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_61);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_ctor_get(x_62, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_62, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_82 = x_62;
} else {
 lean_dec_ref(x_62);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_84 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_84;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Level_param___override(x_5);
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
x_11 = l_Lean_Level_param___override(x_9);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
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
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic '", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' evaluated that the proposition", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nis false", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' failed. Error: ", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_4 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_10 = l_Lean_MessageData_ofName(x_1);
x_11 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__4;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_indentExpr(x_2);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__6;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_20 = l_Lean_MessageData_ofName(x_1);
x_21 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__8;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Exception_toMessageData(x_3);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' failed, could not evaluate decidable instance. Error: ", 56, 56);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConst___at_Lean_Meta_evalExprCore___spec__1___rarg(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_6(x_2, x_10, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = l_Lean_Exception_isInterrupt(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Exception_isRuntime(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = l_Lean_MessageData_ofName(x_3);
x_18 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Exception_toMessageData(x_14);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_25);
return x_9;
}
else
{
lean_dec(x_3);
return x_9;
}
}
else
{
lean_dec(x_3);
return x_9;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = l_Lean_Exception_isInterrupt(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = l_Lean_MessageData_ofName(x_3);
x_31 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__2;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Exception_toMessageData(x_26);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_3);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_27);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_3);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_27);
return x_41;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__3;
x_2 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_nativeDecide", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__7;
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__10;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__11;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_decide_eq_true", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofReduceBool", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__16;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__17;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_12 = l_Lean_Meta_mkDecide(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__4;
lean_inc(x_2);
x_17 = l_Lean_CollectLevelParams_main(x_2, x_16);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_array_to_list(x_18);
x_20 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__6;
lean_inc(x_5);
x_21 = l_Lean_Elab_Term_mkAuxName(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__9;
lean_inc(x_19);
lean_inc(x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_15);
x_27 = lean_box(1);
x_28 = 1;
lean_inc(x_13);
x_29 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_10);
lean_inc(x_9);
x_31 = l_Lean_addAndCompile(x_30, x_9, x_10, x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_34 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__12;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_35 = l_Lean_Meta_mkEqRefl(x_34, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_19);
x_38 = l_List_mapTR_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__1(x_19, x_15);
lean_inc(x_38);
lean_inc(x_22);
x_39 = l_Lean_Expr_const___override(x_22, x_38);
x_40 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__18;
x_41 = l_Lean_mkApp3(x_40, x_39, x_34, x_36);
x_42 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__15;
lean_inc(x_2);
x_43 = l_Lean_mkApp3(x_42, x_2, x_33, x_41);
x_44 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_47 = l_Lean_Meta_mkAuxLemma(x_19, x_2, x_43, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_45);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lean_Expr_const___override(x_49, x_38);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_53 = l_Lean_Expr_const___override(x_51, x_38);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_38);
x_55 = !lean_is_exclusive(x_47);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_47, 0);
x_57 = lean_ctor_get(x_47, 1);
x_58 = l_Lean_Exception_isInterrupt(x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Exception_isRuntime(x_56);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; uint8_t x_62; 
lean_free_object(x_47);
x_60 = 0;
x_61 = l_Lean_Elab_Tactic_SavedState_restore(x_45, x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_63 = lean_ctor_get(x_61, 1);
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
lean_inc(x_2);
lean_inc(x_1);
x_65 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___boxed), 9, 3);
lean_closure_set(x_65, 0, x_1);
lean_closure_set(x_65, 1, x_2);
lean_closure_set(x_65, 2, x_56);
x_66 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___boxed), 8, 3);
lean_closure_set(x_66, 0, x_22);
lean_closure_set(x_66, 1, x_65);
lean_closure_set(x_66, 2, x_1);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 1, x_15);
lean_ctor_set(x_61, 0, x_2);
x_67 = lean_array_mk(x_61);
x_68 = l_Lean_MessageData_ofLazyM(x_66, x_67);
x_69 = l_Lean_throwError___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__2(x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
return x_69;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_69);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_61, 1);
lean_inc(x_74);
lean_dec(x_61);
lean_inc(x_2);
lean_inc(x_1);
x_75 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___boxed), 9, 3);
lean_closure_set(x_75, 0, x_1);
lean_closure_set(x_75, 1, x_2);
lean_closure_set(x_75, 2, x_56);
x_76 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___boxed), 8, 3);
lean_closure_set(x_76, 0, x_22);
lean_closure_set(x_76, 1, x_75);
lean_closure_set(x_76, 2, x_1);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_15);
x_78 = lean_array_mk(x_77);
x_79 = l_Lean_MessageData_ofLazyM(x_76, x_78);
x_80 = l_Lean_throwError___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__2(x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_74);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_dec(x_45);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_47;
}
}
else
{
lean_dec(x_45);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_47;
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_47, 0);
x_86 = lean_ctor_get(x_47, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_47);
x_87 = l_Lean_Exception_isInterrupt(x_85);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Exception_isRuntime(x_85);
if (x_88 == 0)
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_89 = 0;
x_90 = l_Lean_Elab_Tactic_SavedState_restore(x_45, x_89, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_86);
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
lean_inc(x_2);
lean_inc(x_1);
x_93 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___boxed), 9, 3);
lean_closure_set(x_93, 0, x_1);
lean_closure_set(x_93, 1, x_2);
lean_closure_set(x_93, 2, x_85);
x_94 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___boxed), 8, 3);
lean_closure_set(x_94, 0, x_22);
lean_closure_set(x_94, 1, x_93);
lean_closure_set(x_94, 2, x_1);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_92;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_2);
lean_ctor_set(x_95, 1, x_15);
x_96 = lean_array_mk(x_95);
x_97 = l_Lean_MessageData_ofLazyM(x_94, x_96);
x_98 = l_Lean_throwError___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__2(x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
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
else
{
lean_object* x_103; 
lean_dec(x_45);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_85);
lean_ctor_set(x_103, 1, x_86);
return x_103;
}
}
else
{
lean_object* x_104; 
lean_dec(x_45);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_85);
lean_ctor_set(x_104, 1, x_86);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_33);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_35);
if (x_105 == 0)
{
return x_35;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_35, 0);
x_107 = lean_ctor_get(x_35, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_35);
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
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_31);
if (x_109 == 0)
{
return x_31;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_31, 0);
x_111 = lean_ctor_get(x_31, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_31);
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
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_21);
if (x_113 == 0)
{
return x_21;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_21, 0);
x_115 = lean_ctor_get(x_21, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_21);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_12);
if (x_117 == 0)
{
return x_12;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_12, 0);
x_119 = lean_ctor_get(x_12, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_12);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_mkSimpCongrTheorem___spec__1(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_15 = lean_infer_type(x_13, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Meta_isClass_x3f(x_16, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__3;
x_22 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_IR_IRType_beq___spec__1(x_19, x_21);
lean_dec(x_19);
if (x_22 == 0)
{
size_t x_23; size_t x_24; 
lean_dec(x_13);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_9 = x_20;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_26 = l_Lean_MessageData_ofConst(x_13);
x_27 = l_Lean_Elab_Tactic_refineCore___lambda__3___closed__6;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_array_push(x_4, x_29);
x_31 = 1;
x_32 = lean_usize_add(x_2, x_31);
x_2 = x_32;
x_4 = x_30;
x_9 = x_20;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
return x_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_9);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
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
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_usize_of_nat(x_2);
x_17 = lean_usize_of_nat(x_3);
x_18 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__3(x_1, x_16, x_17, x_18, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
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
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
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
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__5___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_11 = lean_ctor_get(x_7, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_dec(x_12);
x_13 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__1;
x_14 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_13);
lean_ctor_set(x_7, 4, x_14);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*12, x_2);
x_131 = l_Lean_isDiagnosticsEnabled(x_7, x_8, x_9);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_15 = x_134;
goto block_130;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_st_ref_take(x_3, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = !lean_is_exclusive(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_137, 4);
lean_dec(x_140);
x_141 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__5;
lean_ctor_set(x_137, 4, x_141);
x_142 = lean_st_ref_set(x_3, x_137, x_138);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_15 = x_143;
goto block_130;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_144 = lean_ctor_get(x_137, 0);
x_145 = lean_ctor_get(x_137, 1);
x_146 = lean_ctor_get(x_137, 2);
x_147 = lean_ctor_get(x_137, 3);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_137);
x_148 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__5;
x_149 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_149, 0, x_144);
lean_ctor_set(x_149, 1, x_145);
lean_ctor_set(x_149, 2, x_146);
lean_ctor_set(x_149, 3, x_147);
lean_ctor_set(x_149, 4, x_148);
x_150 = lean_st_ref_set(x_3, x_149, x_138);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_15 = x_151;
goto block_130;
}
}
block_130:
{
lean_object* x_16; lean_object* x_17; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_4, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_4, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_4, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_4, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_4, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_4, 5);
lean_inc(x_72);
x_73 = !lean_is_exclusive(x_67);
if (x_73 == 0)
{
uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; 
x_74 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_75 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_76 = lean_ctor_get_uint8(x_67, 9);
x_77 = 1;
x_78 = l_Lean_Meta_TransparencyMode_lt(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_68);
lean_ctor_set(x_79, 2, x_69);
lean_ctor_set(x_79, 3, x_70);
lean_ctor_set(x_79, 4, x_71);
lean_ctor_set(x_79, 5, x_72);
lean_ctor_set_uint8(x_79, sizeof(void*)*6, x_74);
lean_ctor_set_uint8(x_79, sizeof(void*)*6 + 1, x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_80 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_5, x_79, x_3, x_7, x_8, x_15);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_16 = x_81;
x_17 = x_82;
goto block_66;
}
else
{
uint8_t x_83; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_83 = !lean_is_exclusive(x_80);
if (x_83 == 0)
{
return x_80;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_80, 0);
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_80);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_ctor_set_uint8(x_67, 9, x_77);
x_87 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_87, 0, x_67);
lean_ctor_set(x_87, 1, x_68);
lean_ctor_set(x_87, 2, x_69);
lean_ctor_set(x_87, 3, x_70);
lean_ctor_set(x_87, 4, x_71);
lean_ctor_set(x_87, 5, x_72);
lean_ctor_set_uint8(x_87, sizeof(void*)*6, x_74);
lean_ctor_set_uint8(x_87, sizeof(void*)*6 + 1, x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_88 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_5, x_87, x_3, x_7, x_8, x_15);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_16 = x_89;
x_17 = x_90;
goto block_66;
}
else
{
uint8_t x_91; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; 
x_95 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_96 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_97 = lean_ctor_get_uint8(x_67, 0);
x_98 = lean_ctor_get_uint8(x_67, 1);
x_99 = lean_ctor_get_uint8(x_67, 2);
x_100 = lean_ctor_get_uint8(x_67, 3);
x_101 = lean_ctor_get_uint8(x_67, 4);
x_102 = lean_ctor_get_uint8(x_67, 5);
x_103 = lean_ctor_get_uint8(x_67, 6);
x_104 = lean_ctor_get_uint8(x_67, 7);
x_105 = lean_ctor_get_uint8(x_67, 8);
x_106 = lean_ctor_get_uint8(x_67, 9);
x_107 = lean_ctor_get_uint8(x_67, 10);
x_108 = lean_ctor_get_uint8(x_67, 11);
x_109 = lean_ctor_get_uint8(x_67, 12);
lean_dec(x_67);
x_110 = 1;
x_111 = l_Lean_Meta_TransparencyMode_lt(x_106, x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_112, 0, x_97);
lean_ctor_set_uint8(x_112, 1, x_98);
lean_ctor_set_uint8(x_112, 2, x_99);
lean_ctor_set_uint8(x_112, 3, x_100);
lean_ctor_set_uint8(x_112, 4, x_101);
lean_ctor_set_uint8(x_112, 5, x_102);
lean_ctor_set_uint8(x_112, 6, x_103);
lean_ctor_set_uint8(x_112, 7, x_104);
lean_ctor_set_uint8(x_112, 8, x_105);
lean_ctor_set_uint8(x_112, 9, x_106);
lean_ctor_set_uint8(x_112, 10, x_107);
lean_ctor_set_uint8(x_112, 11, x_108);
lean_ctor_set_uint8(x_112, 12, x_109);
x_113 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_68);
lean_ctor_set(x_113, 2, x_69);
lean_ctor_set(x_113, 3, x_70);
lean_ctor_set(x_113, 4, x_71);
lean_ctor_set(x_113, 5, x_72);
lean_ctor_set_uint8(x_113, sizeof(void*)*6, x_95);
lean_ctor_set_uint8(x_113, sizeof(void*)*6 + 1, x_96);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_114 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_5, x_113, x_3, x_7, x_8, x_15);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_16 = x_115;
x_17 = x_116;
goto block_66;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_119 = x_114;
} else {
 lean_dec_ref(x_114);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_121, 0, x_97);
lean_ctor_set_uint8(x_121, 1, x_98);
lean_ctor_set_uint8(x_121, 2, x_99);
lean_ctor_set_uint8(x_121, 3, x_100);
lean_ctor_set_uint8(x_121, 4, x_101);
lean_ctor_set_uint8(x_121, 5, x_102);
lean_ctor_set_uint8(x_121, 6, x_103);
lean_ctor_set_uint8(x_121, 7, x_104);
lean_ctor_set_uint8(x_121, 8, x_105);
lean_ctor_set_uint8(x_121, 9, x_110);
lean_ctor_set_uint8(x_121, 10, x_107);
lean_ctor_set_uint8(x_121, 11, x_108);
lean_ctor_set_uint8(x_121, 12, x_109);
x_122 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_68);
lean_ctor_set(x_122, 2, x_69);
lean_ctor_set(x_122, 3, x_70);
lean_ctor_set(x_122, 4, x_71);
lean_ctor_set(x_122, 5, x_72);
lean_ctor_set_uint8(x_122, sizeof(void*)*6, x_95);
lean_ctor_set_uint8(x_122, sizeof(void*)*6 + 1, x_96);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_123 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_5, x_122, x_3, x_7, x_8, x_15);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_16 = x_124;
x_17 = x_125;
goto block_66;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_128 = x_123;
} else {
 lean_dec_ref(x_123);
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
block_66:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_st_ref_get(x_3, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 4);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__2;
x_25 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_26 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_24, x_23, x_25);
lean_dec(x_23);
x_27 = lean_array_get_size(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_27, x_28);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__9(x_26, x_30, x_29);
lean_dec(x_29);
x_32 = lean_array_get_size(x_31);
x_33 = l_Array_filterMapM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__2(x_31, x_30, x_32, x_4, x_3, x_7, x_8, x_21);
lean_dec(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_18, 1, x_35);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_33, 0, x_18);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_18, 1, x_36);
lean_ctor_set(x_18, 0, x_16);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_18);
lean_dec(x_16);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_ctor_get(x_43, 4);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__2;
x_48 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_49 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_47, x_46, x_48);
lean_dec(x_46);
x_50 = lean_array_get_size(x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_50, x_51);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__9(x_49, x_53, x_52);
lean_dec(x_52);
x_55 = lean_array_get_size(x_54);
x_56 = l_Array_filterMapM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__2(x_54, x_53, x_55, x_4, x_3, x_7, x_8, x_44);
lean_dec(x_55);
lean_dec(x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
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
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_16);
lean_ctor_set(x_60, 1, x_57);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_16);
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
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
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_152 = lean_ctor_get(x_7, 0);
x_153 = lean_ctor_get(x_7, 1);
x_154 = lean_ctor_get(x_7, 3);
x_155 = lean_ctor_get(x_7, 5);
x_156 = lean_ctor_get(x_7, 6);
x_157 = lean_ctor_get(x_7, 7);
x_158 = lean_ctor_get(x_7, 8);
x_159 = lean_ctor_get(x_7, 9);
x_160 = lean_ctor_get(x_7, 10);
x_161 = lean_ctor_get(x_7, 11);
x_162 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_7);
x_163 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__1;
x_164 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_163);
x_165 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_165, 0, x_152);
lean_ctor_set(x_165, 1, x_153);
lean_ctor_set(x_165, 2, x_1);
lean_ctor_set(x_165, 3, x_154);
lean_ctor_set(x_165, 4, x_164);
lean_ctor_set(x_165, 5, x_155);
lean_ctor_set(x_165, 6, x_156);
lean_ctor_set(x_165, 7, x_157);
lean_ctor_set(x_165, 8, x_158);
lean_ctor_set(x_165, 9, x_159);
lean_ctor_set(x_165, 10, x_160);
lean_ctor_set(x_165, 11, x_161);
lean_ctor_set_uint8(x_165, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_165, sizeof(void*)*12 + 1, x_162);
x_238 = l_Lean_isDiagnosticsEnabled(x_165, x_8, x_9);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec(x_238);
x_166 = x_241;
goto block_237;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_242 = lean_ctor_get(x_238, 1);
lean_inc(x_242);
lean_dec(x_238);
x_243 = lean_st_ref_take(x_3, x_242);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_244, 2);
lean_inc(x_248);
x_249 = lean_ctor_get(x_244, 3);
lean_inc(x_249);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 lean_ctor_release(x_244, 2);
 lean_ctor_release(x_244, 3);
 lean_ctor_release(x_244, 4);
 x_250 = x_244;
} else {
 lean_dec_ref(x_244);
 x_250 = lean_box(0);
}
x_251 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__5;
if (lean_is_scalar(x_250)) {
 x_252 = lean_alloc_ctor(0, 5, 0);
} else {
 x_252 = x_250;
}
lean_ctor_set(x_252, 0, x_246);
lean_ctor_set(x_252, 1, x_247);
lean_ctor_set(x_252, 2, x_248);
lean_ctor_set(x_252, 3, x_249);
lean_ctor_set(x_252, 4, x_251);
x_253 = lean_st_ref_set(x_3, x_252, x_245);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_166 = x_254;
goto block_237;
}
block_237:
{
lean_object* x_167; lean_object* x_168; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; lean_object* x_216; uint8_t x_217; uint8_t x_218; 
x_195 = lean_ctor_get(x_4, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_4, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_4, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_4, 3);
lean_inc(x_198);
x_199 = lean_ctor_get(x_4, 4);
lean_inc(x_199);
x_200 = lean_ctor_get(x_4, 5);
lean_inc(x_200);
x_201 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_202 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_203 = lean_ctor_get_uint8(x_195, 0);
x_204 = lean_ctor_get_uint8(x_195, 1);
x_205 = lean_ctor_get_uint8(x_195, 2);
x_206 = lean_ctor_get_uint8(x_195, 3);
x_207 = lean_ctor_get_uint8(x_195, 4);
x_208 = lean_ctor_get_uint8(x_195, 5);
x_209 = lean_ctor_get_uint8(x_195, 6);
x_210 = lean_ctor_get_uint8(x_195, 7);
x_211 = lean_ctor_get_uint8(x_195, 8);
x_212 = lean_ctor_get_uint8(x_195, 9);
x_213 = lean_ctor_get_uint8(x_195, 10);
x_214 = lean_ctor_get_uint8(x_195, 11);
x_215 = lean_ctor_get_uint8(x_195, 12);
if (lean_is_exclusive(x_195)) {
 x_216 = x_195;
} else {
 lean_dec_ref(x_195);
 x_216 = lean_box(0);
}
x_217 = 1;
x_218 = l_Lean_Meta_TransparencyMode_lt(x_212, x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
if (lean_is_scalar(x_216)) {
 x_219 = lean_alloc_ctor(0, 0, 13);
} else {
 x_219 = x_216;
}
lean_ctor_set_uint8(x_219, 0, x_203);
lean_ctor_set_uint8(x_219, 1, x_204);
lean_ctor_set_uint8(x_219, 2, x_205);
lean_ctor_set_uint8(x_219, 3, x_206);
lean_ctor_set_uint8(x_219, 4, x_207);
lean_ctor_set_uint8(x_219, 5, x_208);
lean_ctor_set_uint8(x_219, 6, x_209);
lean_ctor_set_uint8(x_219, 7, x_210);
lean_ctor_set_uint8(x_219, 8, x_211);
lean_ctor_set_uint8(x_219, 9, x_212);
lean_ctor_set_uint8(x_219, 10, x_213);
lean_ctor_set_uint8(x_219, 11, x_214);
lean_ctor_set_uint8(x_219, 12, x_215);
x_220 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_196);
lean_ctor_set(x_220, 2, x_197);
lean_ctor_set(x_220, 3, x_198);
lean_ctor_set(x_220, 4, x_199);
lean_ctor_set(x_220, 5, x_200);
lean_ctor_set_uint8(x_220, sizeof(void*)*6, x_201);
lean_ctor_set_uint8(x_220, sizeof(void*)*6 + 1, x_202);
lean_inc(x_8);
lean_inc(x_165);
lean_inc(x_3);
x_221 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_5, x_220, x_3, x_165, x_8, x_166);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_167 = x_222;
x_168 = x_223;
goto block_194;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_165);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_224 = lean_ctor_get(x_221, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_226 = x_221;
} else {
 lean_dec_ref(x_221);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
if (lean_is_scalar(x_216)) {
 x_228 = lean_alloc_ctor(0, 0, 13);
} else {
 x_228 = x_216;
}
lean_ctor_set_uint8(x_228, 0, x_203);
lean_ctor_set_uint8(x_228, 1, x_204);
lean_ctor_set_uint8(x_228, 2, x_205);
lean_ctor_set_uint8(x_228, 3, x_206);
lean_ctor_set_uint8(x_228, 4, x_207);
lean_ctor_set_uint8(x_228, 5, x_208);
lean_ctor_set_uint8(x_228, 6, x_209);
lean_ctor_set_uint8(x_228, 7, x_210);
lean_ctor_set_uint8(x_228, 8, x_211);
lean_ctor_set_uint8(x_228, 9, x_217);
lean_ctor_set_uint8(x_228, 10, x_213);
lean_ctor_set_uint8(x_228, 11, x_214);
lean_ctor_set_uint8(x_228, 12, x_215);
x_229 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_196);
lean_ctor_set(x_229, 2, x_197);
lean_ctor_set(x_229, 3, x_198);
lean_ctor_set(x_229, 4, x_199);
lean_ctor_set(x_229, 5, x_200);
lean_ctor_set_uint8(x_229, sizeof(void*)*6, x_201);
lean_ctor_set_uint8(x_229, sizeof(void*)*6 + 1, x_202);
lean_inc(x_8);
lean_inc(x_165);
lean_inc(x_3);
x_230 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure(x_5, x_229, x_3, x_165, x_8, x_166);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_167 = x_231;
x_168 = x_232;
goto block_194;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_165);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_230, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_235 = x_230;
} else {
 lean_dec_ref(x_230);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
block_194:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_169 = lean_st_ref_get(x_3, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
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
x_173 = lean_ctor_get(x_170, 4);
lean_inc(x_173);
lean_dec(x_170);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec(x_173);
x_175 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__2;
x_176 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_177 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_175, x_174, x_176);
lean_dec(x_174);
x_178 = lean_array_get_size(x_177);
x_179 = lean_unsigned_to_nat(1u);
x_180 = lean_nat_sub(x_178, x_179);
lean_dec(x_178);
x_181 = lean_unsigned_to_nat(0u);
x_182 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__9(x_177, x_181, x_180);
lean_dec(x_180);
x_183 = lean_array_get_size(x_182);
x_184 = l_Array_filterMapM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__2(x_182, x_181, x_183, x_4, x_3, x_165, x_8, x_171);
lean_dec(x_183);
lean_dec(x_182);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_172;
}
lean_ctor_set(x_188, 0, x_167);
lean_ctor_set(x_188, 1, x_185);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_186);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_172);
lean_dec(x_167);
x_190 = lean_ctor_get(x_184, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_184, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_192 = x_184;
} else {
 lean_dec_ref(x_184);
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
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__1;
x_9 = 1;
x_10 = l_Lean_Option_set___at_Lean_Meta_getEqnsFor_x3f___spec__1(x_7, x_8, x_9);
x_11 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_10, x_8);
x_12 = lean_st_ref_get(x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Kernel_isDiagnosticsEnabled(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
if (x_11 == 0)
{
x_17 = x_9;
goto block_45;
}
else
{
uint8_t x_46; 
x_46 = 0;
x_17 = x_46;
goto block_45;
}
}
else
{
if (x_11 == 0)
{
uint8_t x_47; 
x_47 = 0;
x_17 = x_47;
goto block_45;
}
else
{
x_17 = x_9;
goto block_45;
}
}
block_45:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_st_ref_take(x_5, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 4);
lean_dec(x_23);
x_24 = l_Lean_Kernel_enableDiag(x_22, x_11);
x_25 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__2;
lean_ctor_set(x_19, 4, x_25);
lean_ctor_set(x_19, 0, x_24);
x_26 = lean_st_ref_set(x_5, x_19, x_20);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2(x_10, x_11, x_3, x_2, x_1, x_28, x_4, x_5, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
x_32 = lean_ctor_get(x_19, 2);
x_33 = lean_ctor_get(x_19, 3);
x_34 = lean_ctor_get(x_19, 5);
x_35 = lean_ctor_get(x_19, 6);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_36 = l_Lean_Kernel_enableDiag(x_30, x_11);
x_37 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__2;
x_38 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_38, 2, x_32);
lean_ctor_set(x_38, 3, x_33);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_34);
lean_ctor_set(x_38, 6, x_35);
x_39 = lean_st_ref_set(x_5, x_38, x_20);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2(x_10, x_11, x_3, x_2, x_1, x_41, x_4, x_5, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2(x_10, x_11, x_3, x_2, x_1, x_43, x_4, x_5, x_14);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__1;
x_2 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' failed for proposition", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nsince its '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__2;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instance", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ndid not reduce to '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' or '", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__15() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__7;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'.\n\n", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Classical", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("choice", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__18;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__19;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nHint: Reduction got stuck on '", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__23() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__20;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__22;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__23;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', which indicates that a '", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__25;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__24;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__26;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__27;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instance is defined using classical reasoning, proving an instance exists rather than giving a concrete construction. The '", 125, 125);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__29;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__28;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__30;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' tactic works by evaluating a decision procedure via reduction, and it cannot make progress with such instances. This can occur due to the 'opened scoped Classical' command, which enables the instance '", 203, 203);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__32;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("propDecidable", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__18;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__34;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__36() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__35;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'.", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__37;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nHint: Reduction got stuck on '▸' (", 38, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__39;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__41() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__2;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__40;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__41;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("), which suggests that one of the '", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__43;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__42;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__44;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__45;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__47() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instances is defined using tactics such as 'rw' or 'simp'. To avoid tactics, make use of functions such as '", 110, 110);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__47;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__46;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__48;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inferInstanceAs", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__50;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__52() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__51;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__49;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__52;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__53;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__14;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__55() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decidable_of_decidable_of_iff", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__55;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__57() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__56;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__54;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__57;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__59() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to alter a proposition.", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__59;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__58;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__60;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__62() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("After unfolding the ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__62;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__64() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__64;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__66() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", reduction got stuck at the '", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__66;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__68() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instances", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__68;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__63;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__69;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__70;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__65;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__72() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instance", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__72;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__63;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__73;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__74;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__65;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__76() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Reduction got stuck at the '", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__76;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__77;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__78;
x_2 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__9;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3), 6, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_withoutModifyingState___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__4(x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = l_Array_isEmpty___rarg(x_17);
x_19 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__2;
x_20 = l_Lean_Expr_isAppOf(x_16, x_19);
x_21 = l_Lean_MessageData_ofName(x_2);
x_22 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2;
lean_inc(x_21);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_22);
x_23 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_indentExpr(x_3);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__6;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__9;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_indentExpr(x_1);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__11;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__12;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__14;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__15;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__17;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
if (x_18 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_array_get_size(x_17);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_dec_eq(x_71, x_72);
lean_dec(x_71);
x_74 = lean_array_to_list(x_17);
x_75 = l_Lean_MessageData_andList(x_74);
lean_inc(x_16);
x_76 = l_Lean_indentExpr(x_16);
if (x_73 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__71;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
x_79 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__67;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_29);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_31);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_76);
x_84 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_45 = x_85;
goto block_70;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__75;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_75);
x_88 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__67;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_29);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_31);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_76);
x_93 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_45 = x_94;
goto block_70;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_17);
lean_inc(x_16);
x_95 = l_Lean_indentExpr(x_16);
x_96 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__79;
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_45 = x_99;
goto block_70;
}
block_70:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
if (x_20 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__20;
x_50 = l_Lean_Expr_isAppOf(x_16, x_49);
lean_dec(x_16);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_21);
x_51 = l_Lean_MessageData_nil;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
if (lean_is_scalar(x_14)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_14;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_13);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__31;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_21);
x_57 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__33;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__36;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__38;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_48);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_47);
if (lean_is_scalar(x_14)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_14;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_13);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_21);
lean_dec(x_16);
x_66 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__61;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_48);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_47);
if (lean_is_scalar(x_14)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_14;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_13);
return x_69;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_100 = lean_ctor_get(x_12, 0);
x_101 = lean_ctor_get(x_12, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_12);
x_102 = l_Array_isEmpty___rarg(x_101);
x_103 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__2;
x_104 = l_Lean_Expr_isAppOf(x_100, x_103);
x_105 = l_Lean_MessageData_ofName(x_2);
x_106 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2;
lean_inc(x_105);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__4;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_indentExpr(x_3);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__6;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__9;
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_indentExpr(x_1);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__11;
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__12;
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__14;
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__15;
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__17;
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
if (x_102 == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_156 = lean_array_get_size(x_101);
x_157 = lean_unsigned_to_nat(1u);
x_158 = lean_nat_dec_eq(x_156, x_157);
lean_dec(x_156);
x_159 = lean_array_to_list(x_101);
x_160 = l_Lean_MessageData_andList(x_159);
lean_inc(x_100);
x_161 = l_Lean_indentExpr(x_100);
if (x_158 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_162 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__71;
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
x_164 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__67;
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_114);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_116);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_161);
x_169 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_130 = x_170;
goto block_155;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_171 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__75;
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_160);
x_173 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__67;
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_114);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_116);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_161);
x_178 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_130 = x_179;
goto block_155;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_101);
lean_inc(x_100);
x_180 = l_Lean_indentExpr(x_100);
x_181 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__79;
x_182 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
x_183 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_130 = x_184;
goto block_155;
}
block_155:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
if (x_104 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__20;
x_135 = l_Lean_Expr_isAppOf(x_100, x_134);
lean_dec(x_100);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_105);
x_136 = l_Lean_MessageData_nil;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_132);
if (lean_is_scalar(x_14)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_14;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_13);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_140 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__31;
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_105);
x_142 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__33;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__36;
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__38;
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_133);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_132);
if (lean_is_scalar(x_14)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_14;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_13);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_105);
lean_dec(x_100);
x_151 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__61;
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_133);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_132);
if (lean_is_scalar(x_14)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_14;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_13);
return x_154;
}
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_11);
if (x_185 == 0)
{
return x_11;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_11, 0);
x_187 = lean_ctor_get(x_11, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_11);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' proved that the proposition", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' failed. internal error: the elaborator is able to reduce the '", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' instance, but the kernel is not able to", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_5, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_5, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_5, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_5, 4);
lean_inc(x_43);
x_44 = lean_ctor_get(x_5, 5);
lean_inc(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; 
x_46 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_47 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 1);
x_48 = lean_ctor_get_uint8(x_39, 9);
x_49 = 1;
x_50 = l_Lean_Meta_TransparencyMode_lt(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_42);
lean_ctor_set(x_51, 4, x_43);
lean_ctor_set(x_51, 5, x_44);
lean_ctor_set_uint8(x_51, sizeof(void*)*6, x_46);
lean_ctor_set_uint8(x_51, sizeof(void*)*6 + 1, x_47);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_52 = lean_whnf(x_1, x_51, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_10 = x_53;
x_11 = x_54;
goto block_38;
}
else
{
uint8_t x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_ctor_set_uint8(x_39, 9, x_49);
x_59 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_40);
lean_ctor_set(x_59, 2, x_41);
lean_ctor_set(x_59, 3, x_42);
lean_ctor_set(x_59, 4, x_43);
lean_ctor_set(x_59, 5, x_44);
lean_ctor_set_uint8(x_59, sizeof(void*)*6, x_46);
lean_ctor_set_uint8(x_59, sizeof(void*)*6 + 1, x_47);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_60 = lean_whnf(x_1, x_59, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_10 = x_61;
x_11 = x_62;
goto block_38;
}
else
{
uint8_t x_63; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
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
uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; 
x_67 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_68 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 1);
x_69 = lean_ctor_get_uint8(x_39, 0);
x_70 = lean_ctor_get_uint8(x_39, 1);
x_71 = lean_ctor_get_uint8(x_39, 2);
x_72 = lean_ctor_get_uint8(x_39, 3);
x_73 = lean_ctor_get_uint8(x_39, 4);
x_74 = lean_ctor_get_uint8(x_39, 5);
x_75 = lean_ctor_get_uint8(x_39, 6);
x_76 = lean_ctor_get_uint8(x_39, 7);
x_77 = lean_ctor_get_uint8(x_39, 8);
x_78 = lean_ctor_get_uint8(x_39, 9);
x_79 = lean_ctor_get_uint8(x_39, 10);
x_80 = lean_ctor_get_uint8(x_39, 11);
x_81 = lean_ctor_get_uint8(x_39, 12);
lean_dec(x_39);
x_82 = 1;
x_83 = l_Lean_Meta_TransparencyMode_lt(x_78, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_84, 0, x_69);
lean_ctor_set_uint8(x_84, 1, x_70);
lean_ctor_set_uint8(x_84, 2, x_71);
lean_ctor_set_uint8(x_84, 3, x_72);
lean_ctor_set_uint8(x_84, 4, x_73);
lean_ctor_set_uint8(x_84, 5, x_74);
lean_ctor_set_uint8(x_84, 6, x_75);
lean_ctor_set_uint8(x_84, 7, x_76);
lean_ctor_set_uint8(x_84, 8, x_77);
lean_ctor_set_uint8(x_84, 9, x_78);
lean_ctor_set_uint8(x_84, 10, x_79);
lean_ctor_set_uint8(x_84, 11, x_80);
lean_ctor_set_uint8(x_84, 12, x_81);
x_85 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_40);
lean_ctor_set(x_85, 2, x_41);
lean_ctor_set(x_85, 3, x_42);
lean_ctor_set(x_85, 4, x_43);
lean_ctor_set(x_85, 5, x_44);
lean_ctor_set_uint8(x_85, sizeof(void*)*6, x_67);
lean_ctor_set_uint8(x_85, sizeof(void*)*6 + 1, x_68);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_86 = lean_whnf(x_1, x_85, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_10 = x_87;
x_11 = x_88;
goto block_38;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_91 = x_86;
} else {
 lean_dec_ref(x_86);
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
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_93, 0, x_69);
lean_ctor_set_uint8(x_93, 1, x_70);
lean_ctor_set_uint8(x_93, 2, x_71);
lean_ctor_set_uint8(x_93, 3, x_72);
lean_ctor_set_uint8(x_93, 4, x_73);
lean_ctor_set_uint8(x_93, 5, x_74);
lean_ctor_set_uint8(x_93, 6, x_75);
lean_ctor_set_uint8(x_93, 7, x_76);
lean_ctor_set_uint8(x_93, 8, x_77);
lean_ctor_set_uint8(x_93, 9, x_82);
lean_ctor_set_uint8(x_93, 10, x_79);
lean_ctor_set_uint8(x_93, 11, x_80);
lean_ctor_set_uint8(x_93, 12, x_81);
x_94 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_40);
lean_ctor_set(x_94, 2, x_41);
lean_ctor_set(x_94, 3, x_42);
lean_ctor_set(x_94, 4, x_43);
lean_ctor_set(x_94, 5, x_44);
lean_ctor_set_uint8(x_94, sizeof(void*)*6, x_67);
lean_ctor_set_uint8(x_94, sizeof(void*)*6 + 1, x_68);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_95 = lean_whnf(x_1, x_94, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_10 = x_96;
x_11 = x_97;
goto block_38;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_100 = x_95;
} else {
 lean_dec_ref(x_95);
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
}
else
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_4, 0);
lean_inc(x_102);
lean_dec(x_4);
x_10 = x_102;
x_11 = x_9;
goto block_38;
}
block_38:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5;
x_13 = l_Lean_Expr_isAppOf(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__7;
x_15 = l_Lean_Expr_isAppOf(x_10, x_14);
lean_dec(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_18 = l_Lean_MessageData_ofName(x_2);
x_19 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_3);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__6;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_28 = l_Lean_MessageData_ofName(x_2);
x_29 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__6;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5), 9, 4);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_5);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_array_mk(x_17);
x_19 = l_Lean_MessageData_ofLazyM(x_15, x_18);
x_20 = l_Lean_throwError___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__5___rarg(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_filterMapM___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_evalDecideCore_diagnose___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalDecideCore_diagnose(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_12 = l_Lean_Meta_mkDecideProof(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_appFn_x21(x_13);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
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
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*6 + 1);
x_26 = lean_ctor_get_uint8(x_17, 9);
x_27 = 1;
x_28 = l_Lean_Meta_TransparencyMode_lt(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_20);
lean_ctor_set(x_29, 4, x_21);
lean_ctor_set(x_29, 5, x_22);
lean_ctor_set_uint8(x_29, sizeof(void*)*6, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*6 + 1, x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_16);
x_30 = lean_whnf(x_16, x_29, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5;
x_35 = l_Lean_Expr_isAppOf(x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_30);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_32);
x_37 = l_Lean_Elab_Tactic_evalDecideCore_diagnose(x_1, lean_box(0), x_2, x_16, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_37;
}
else
{
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_30, 0, x_13);
return x_30;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5;
x_41 = l_Lean_Expr_isAppOf(x_38, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_13);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_38);
x_43 = l_Lean_Elab_Tactic_evalDecideCore_diagnose(x_1, lean_box(0), x_2, x_16, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_43;
}
else
{
lean_object* x_44; 
lean_dec(x_38);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_13);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_ctor_set_uint8(x_17, 9, x_27);
x_49 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_49, 0, x_17);
lean_ctor_set(x_49, 1, x_18);
lean_ctor_set(x_49, 2, x_19);
lean_ctor_set(x_49, 3, x_20);
lean_ctor_set(x_49, 4, x_21);
lean_ctor_set(x_49, 5, x_22);
lean_ctor_set_uint8(x_49, sizeof(void*)*6, x_24);
lean_ctor_set_uint8(x_49, sizeof(void*)*6 + 1, x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_16);
x_50 = lean_whnf(x_16, x_49, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5;
x_55 = l_Lean_Expr_isAppOf(x_52, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_free_object(x_50);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_52);
x_57 = l_Lean_Elab_Tactic_evalDecideCore_diagnose(x_1, lean_box(0), x_2, x_16, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_57;
}
else
{
lean_dec(x_52);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_50, 0, x_13);
return x_50;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5;
x_61 = l_Lean_Expr_isAppOf(x_58, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_13);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_58);
x_63 = l_Lean_Elab_Tactic_evalDecideCore_diagnose(x_1, lean_box(0), x_2, x_16, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_63;
}
else
{
lean_object* x_64; 
lean_dec(x_58);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_13);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_50);
if (x_65 == 0)
{
return x_50;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_50, 0);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_50);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; 
x_69 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_70 = lean_ctor_get_uint8(x_7, sizeof(void*)*6 + 1);
x_71 = lean_ctor_get_uint8(x_17, 0);
x_72 = lean_ctor_get_uint8(x_17, 1);
x_73 = lean_ctor_get_uint8(x_17, 2);
x_74 = lean_ctor_get_uint8(x_17, 3);
x_75 = lean_ctor_get_uint8(x_17, 4);
x_76 = lean_ctor_get_uint8(x_17, 5);
x_77 = lean_ctor_get_uint8(x_17, 6);
x_78 = lean_ctor_get_uint8(x_17, 7);
x_79 = lean_ctor_get_uint8(x_17, 8);
x_80 = lean_ctor_get_uint8(x_17, 9);
x_81 = lean_ctor_get_uint8(x_17, 10);
x_82 = lean_ctor_get_uint8(x_17, 11);
x_83 = lean_ctor_get_uint8(x_17, 12);
lean_dec(x_17);
x_84 = 1;
x_85 = l_Lean_Meta_TransparencyMode_lt(x_80, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_86, 0, x_71);
lean_ctor_set_uint8(x_86, 1, x_72);
lean_ctor_set_uint8(x_86, 2, x_73);
lean_ctor_set_uint8(x_86, 3, x_74);
lean_ctor_set_uint8(x_86, 4, x_75);
lean_ctor_set_uint8(x_86, 5, x_76);
lean_ctor_set_uint8(x_86, 6, x_77);
lean_ctor_set_uint8(x_86, 7, x_78);
lean_ctor_set_uint8(x_86, 8, x_79);
lean_ctor_set_uint8(x_86, 9, x_80);
lean_ctor_set_uint8(x_86, 10, x_81);
lean_ctor_set_uint8(x_86, 11, x_82);
lean_ctor_set_uint8(x_86, 12, x_83);
x_87 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_18);
lean_ctor_set(x_87, 2, x_19);
lean_ctor_set(x_87, 3, x_20);
lean_ctor_set(x_87, 4, x_21);
lean_ctor_set(x_87, 5, x_22);
lean_ctor_set_uint8(x_87, sizeof(void*)*6, x_69);
lean_ctor_set_uint8(x_87, sizeof(void*)*6 + 1, x_70);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_16);
x_88 = lean_whnf(x_16, x_87, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5;
x_93 = l_Lean_Expr_isAppOf(x_89, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_91);
lean_dec(x_13);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_95 = l_Lean_Elab_Tactic_evalDecideCore_diagnose(x_1, lean_box(0), x_2, x_16, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_95;
}
else
{
lean_object* x_96; 
lean_dec(x_89);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_13);
lean_ctor_set(x_96, 1, x_90);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_ctor_get(x_88, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_99 = x_88;
} else {
 lean_dec_ref(x_88);
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
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_101, 0, x_71);
lean_ctor_set_uint8(x_101, 1, x_72);
lean_ctor_set_uint8(x_101, 2, x_73);
lean_ctor_set_uint8(x_101, 3, x_74);
lean_ctor_set_uint8(x_101, 4, x_75);
lean_ctor_set_uint8(x_101, 5, x_76);
lean_ctor_set_uint8(x_101, 6, x_77);
lean_ctor_set_uint8(x_101, 7, x_78);
lean_ctor_set_uint8(x_101, 8, x_79);
lean_ctor_set_uint8(x_101, 9, x_84);
lean_ctor_set_uint8(x_101, 10, x_81);
lean_ctor_set_uint8(x_101, 11, x_82);
lean_ctor_set_uint8(x_101, 12, x_83);
x_102 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_18);
lean_ctor_set(x_102, 2, x_19);
lean_ctor_set(x_102, 3, x_20);
lean_ctor_set(x_102, 4, x_21);
lean_ctor_set(x_102, 5, x_22);
lean_ctor_set_uint8(x_102, sizeof(void*)*6, x_69);
lean_ctor_set_uint8(x_102, sizeof(void*)*6 + 1, x_70);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_16);
x_103 = lean_whnf(x_16, x_102, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5;
x_108 = l_Lean_Expr_isAppOf(x_104, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_106);
lean_dec(x_13);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_104);
x_110 = l_Lean_Elab_Tactic_evalDecideCore_diagnose(x_1, lean_box(0), x_2, x_16, x_109, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_105);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_110;
}
else
{
lean_object* x_111; 
lean_dec(x_104);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_106)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_106;
}
lean_ctor_set(x_111, 0, x_13);
lean_ctor_set(x_111, 1, x_105);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_114 = x_103;
} else {
 lean_dec_ref(x_103);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_12);
if (x_116 == 0)
{
return x_12;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_12, 0);
x_118 = lean_ctor_get(x_12, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_12);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalDecideCore_doElab(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_Tactic_evalDecideCore_doKernel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
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
x_8 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_6);
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
x_13 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_12 = l_Lean_Meta_mkDecideProof(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_appFn_x21(x_13);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__4;
lean_inc(x_2);
x_19 = l_Lean_CollectLevelParams_main(x_2, x_18);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_Term_getLevelNames___rarg(x_6, x_7, x_8, x_9, x_10, x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_List_reverse___rarg(x_22);
x_25 = l_List_filterTR_loop___at_Lean_Elab_Tactic_evalDecideCore_doKernel___spec__1(x_20, x_24, x_17);
lean_dec(x_20);
x_26 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_25);
x_29 = l_Lean_Meta_mkAuxLemma(x_25, x_2, x_13, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_List_mapTR_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__1(x_25, x_17);
x_33 = l_Lean_Expr_const___override(x_31, x_32);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = l_List_mapTR_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___spec__1(x_25, x_17);
x_37 = l_Lean_Expr_const___override(x_34, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_25);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
x_42 = l_Lean_Exception_isInterrupt(x_40);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Exception_isRuntime(x_40);
if (x_43 == 0)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_free_object(x_29);
lean_dec(x_40);
x_44 = 0;
x_45 = l_Lean_Elab_Tactic_SavedState_restore(x_27, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = l_Lean_Elab_Tactic_evalDecideCore_diagnose(x_1, lean_box(0), x_2, x_16, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
}
else
{
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_29, 0);
x_54 = lean_ctor_get(x_29, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_29);
x_55 = l_Lean_Exception_isInterrupt(x_53);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Exception_isRuntime(x_53);
if (x_56 == 0)
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_53);
x_57 = 0;
x_58 = l_Lean_Elab_Tactic_SavedState_restore(x_27, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_54);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = l_Lean_Elab_Tactic_evalDecideCore_diagnose(x_1, lean_box(0), x_2, x_16, x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
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
else
{
lean_object* x_66; 
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_53);
lean_ctor_set(x_66, 1, x_54);
return x_66;
}
}
else
{
lean_object* x_67; 
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_54);
return x_67;
}
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_12);
if (x_68 == 0)
{
return x_12;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_12, 0);
x_70 = lean_ctor_get(x_12, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_12);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_Tactic_evalDecideCore_doKernel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterTR_loop___at_Lean_Elab_Tactic_evalDecideCore_doKernel___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalDecideCore_doKernel(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_2, 1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_2, 0);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_Elab_Tactic_evalDecideCore_doElab(x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
lean_dec(x_8);
lean_dec(x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_Elab_Tactic_evalDecideCore_doKernel(x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_8);
lean_dec(x_7);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe(x_3, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_8);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' failed, cannot simultaneously set both '+kernel' and '+native'", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_1, 0);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Tactic_evalDecideCore___lambda__1(x_3, x_1, x_2, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_1, 1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Elab_Tactic_evalDecideCore___lambda__1(x_3, x_1, x_2, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_3);
x_20 = l_Lean_MessageData_ofName(x_2);
x_21 = l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lambda__2___boxed), 13, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = 1;
x_15 = l_Lean_Elab_Tactic_closeMainGoalUsing(x_2, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Tactic_filterOldMVars___closed__1;
x_15 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(x_11, x_14, x_15, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = l_Lean_MVarId_getDecl(x_17, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_LocalContext_getFVarIds(x_22);
lean_dec(x_22);
x_24 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_MVarId_revert(x_17, x_23, x_24, x_15, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_13);
lean_ctor_set(x_26, 0, x_29);
x_31 = l_Lean_Elab_Tactic_replaceMainGoal(x_26, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_13);
x_34 = l_Lean_Elab_Tactic_replaceMainGoal(x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
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
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
return x_16;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_10);
if (x_47 == 0)
{
return x_10;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideCore___lambda__4___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, 3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Tactic_evalDecideCore___lambda__3(x_2, x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Elab_Tactic_evalDecideCore___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Elab_Tactic_withMainContext___rarg(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Tactic_evalDecideCore___lambda__3(x_2, x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_17);
return x_19;
}
else
{
uint8_t x_20; 
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
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalDecideCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalDecideCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalDecideCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideCore___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalDecideCore___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("DecideConfig", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__2;
x_10 = 0;
x_11 = l_Lean_Meta_evalExpr_x27___rarg(x_9, x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabDecideConfig___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_14, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_12, 1, x_18);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_22, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nException: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163_(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = l_Lean_Exception_isInterrupt(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Exception_isRuntime(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_10);
x_20 = l_Lean_MessageData_ofExpr(x_1);
x_21 = l_Lean_indentD(x_20);
x_22 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Exception_toMessageData(x_16);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Elab_Tactic_elabDecideConfig___spec__1(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = l_Lean_Exception_isInterrupt(x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Exception_isRuntime(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = l_Lean_MessageData_ofExpr(x_1);
x_40 = l_Lean_indentD(x_39);
x_41 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Exception_toMessageData(x_35);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_Tactic_elabDecideConfig___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_35);
lean_ctor_set(x_54, 1, x_36);
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
lean_dec(x_3);
lean_dec(x_1);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_35);
lean_ctor_set(x_55, 1, x_36);
return x_55;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasSorry(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__2;
x_14 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__3___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 1;
x_3 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_2);
lean_ctor_set_uint8(x_3, 3, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(x_1, x_11, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_hasSyntheticSorry(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_12);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__2(x_14, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__3___closed__1;
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = l_Lean_Expr_hasSyntheticSorry(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__2(x_20, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__3___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
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
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__2;
x_2 = l_Lean_MessageData_ofName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__2;
x_2 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__4;
x_2 = l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__2;
x_16 = l_Lean_Environment_contains(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__5;
x_18 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__3(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_1);
x_12 = l_Lean_Parser_Tactic_getConfigItems(x_1);
x_13 = l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(x_12);
x_14 = l_Array_isEmpty___rarg(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_8, 5);
x_17 = l_Lean_replaceRef(x_1, x_16);
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_8, 5, x_17);
x_18 = lean_box(0);
x_19 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__4(x_11, x_13, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get(x_8, 5);
x_26 = lean_ctor_get(x_8, 6);
x_27 = lean_ctor_get(x_8, 7);
x_28 = lean_ctor_get(x_8, 8);
x_29 = lean_ctor_get(x_8, 9);
x_30 = lean_ctor_get(x_8, 10);
x_31 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_32 = lean_ctor_get(x_8, 11);
x_33 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_32);
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
lean_inc(x_20);
lean_dec(x_8);
x_34 = l_Lean_replaceRef(x_1, x_25);
lean_dec(x_25);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_21);
lean_ctor_set(x_35, 2, x_22);
lean_ctor_set(x_35, 3, x_23);
lean_ctor_set(x_35, 4, x_24);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_26);
lean_ctor_set(x_35, 7, x_27);
lean_ctor_set(x_35, 8, x_28);
lean_ctor_set(x_35, 9, x_29);
lean_ctor_set(x_35, 10, x_30);
lean_ctor_set(x_35, 11, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*12, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*12 + 1, x_33);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__4(x_11, x_13, x_36, x_4, x_5, x_6, x_7, x_35, x_9, x_10);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__3___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabDecideConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Tactic_elabDecideConfig___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabDecideConfig___lambda__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabDecideConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabDecideConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decide", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecide___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalDecide___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Tactic_elabDecideConfig(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Tactic_evalDecide___closed__2;
x_17 = l_Lean_Elab_Tactic_evalDecideCore(x_16, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l_Lean_Elab_Tactic_evalDecide___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalDecide", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecide___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(373u);
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(397u);
x_2 = lean_unsigned_to_nat(74u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(44u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(74u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(373u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(373u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(48u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(58u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideBang___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decide!", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDecideBang___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalDecideBang___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideBang(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Tactic_elabDecideConfig(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 1;
lean_ctor_set_uint8(x_14, 0, x_17);
x_18 = l_Lean_Elab_Tactic_evalDecideBang___closed__2;
x_19 = l_Lean_Elab_Tactic_evalDecideCore(x_18, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_19;
}
else
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get_uint8(x_14, 1);
x_21 = lean_ctor_get_uint8(x_14, 2);
x_22 = lean_ctor_get_uint8(x_14, 3);
lean_dec(x_14);
x_23 = 1;
x_24 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, 1, x_20);
lean_ctor_set_uint8(x_24, 2, x_21);
lean_ctor_set_uint8(x_24, 3, x_22);
x_25 = l_Lean_Elab_Tactic_evalDecideBang___closed__2;
x_26 = l_Lean_Elab_Tactic_evalDecideCore(x_25, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_26;
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDecideBang___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalDecideBang(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decideBang", 10, 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalDecideBang", 14, 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDecideBang___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("native_decide", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalNativeDecide___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalNativeDecide___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalNativeDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Tactic_elabDecideConfig(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 1;
lean_ctor_set_uint8(x_14, 1, x_17);
x_18 = l_Lean_Elab_Tactic_evalNativeDecide___closed__2;
x_19 = l_Lean_Elab_Tactic_evalDecideCore(x_18, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
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
x_25 = l_Lean_Elab_Tactic_evalNativeDecide___closed__2;
x_26 = l_Lean_Elab_Tactic_evalDecideCore(x_25, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_26;
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
lean_dec(x_2);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nativeDecide", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Tactic_evalExact___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalNativeDecide", 16, 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExact___closed__1;
x_2 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2;
x_3 = l_Lean_Elab_Tactic_evalExact___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNativeDecide___boxed), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(410u);
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(417u);
x_2 = lean_unsigned_to_nat(160u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(160u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(410u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(410u);
x_2 = lean_unsigned_to_nat(70u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(54u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(70u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__7;
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
l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__1 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__1);
l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__2);
l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__3 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__3);
l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__4 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__4);
l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__5 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__5);
l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__6 = _init_l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_runTermElab___spec__2___rarg___closed__6);
l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__1);
l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_logUnassignedAndAbort___spec__1___rarg___closed__2);
l_Lean_Elab_Tactic_filterOldMVars___closed__1 = _init_l_Lean_Elab_Tactic_filterOldMVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_filterOldMVars___closed__1);
l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__1);
l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__2);
l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__3);
l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_closeMainGoalUsing___lambda__1___closed__4);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg___closed__2);
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
l_Lean_Elab_Tactic_evalExact___closed__6 = _init_l_Lean_Elab_Tactic_evalExact___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExact___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact__1___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalExact__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalExact_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_refineCore___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lambda__3___closed__1);
l_Lean_Elab_Tactic_refineCore___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lambda__3___closed__2);
l_Lean_Elab_Tactic_refineCore___lambda__3___closed__3 = _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lambda__3___closed__3);
l_Lean_Elab_Tactic_refineCore___lambda__3___closed__4 = _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lambda__3___closed__4);
l_Lean_Elab_Tactic_refineCore___lambda__3___closed__5 = _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lambda__3___closed__5);
l_Lean_Elab_Tactic_refineCore___lambda__3___closed__6 = _init_l_Lean_Elab_Tactic_refineCore___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_refineCore___lambda__3___closed__6);
l_Lean_Elab_Tactic_evalRefine___closed__1 = _init_l_Lean_Elab_Tactic_evalRefine___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___closed__1);
l_Lean_Elab_Tactic_evalRefine___closed__2 = _init_l_Lean_Elab_Tactic_evalRefine___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___closed__2);
l_Lean_Elab_Tactic_evalRefine___closed__3 = _init_l_Lean_Elab_Tactic_evalRefine___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRefine__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRefine_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalRefine_x27___closed__1 = _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___closed__1);
l_Lean_Elab_Tactic_evalRefine_x27___closed__2 = _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___closed__2);
l_Lean_Elab_Tactic_evalRefine_x27___closed__3 = _init_l_Lean_Elab_Tactic_evalRefine_x27___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRefine_x27___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRefine_x27_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__1);
l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___lambda__1___closed__2);
l_Lean_Elab_Tactic_evalSpecialize___closed__1 = _init_l_Lean_Elab_Tactic_evalSpecialize___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___closed__1);
l_Lean_Elab_Tactic_evalSpecialize___closed__2 = _init_l_Lean_Elab_Tactic_evalSpecialize___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___closed__2);
l_Lean_Elab_Tactic_evalSpecialize___closed__3 = _init_l_Lean_Elab_Tactic_evalSpecialize___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___closed__3);
l_Lean_Elab_Tactic_evalSpecialize___closed__4 = _init_l_Lean_Elab_Tactic_evalSpecialize___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSpecialize___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSpecialize_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_elabTermForApply___closed__1 = _init_l_Lean_Elab_Tactic_elabTermForApply___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabTermForApply___closed__1);
l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__1);
l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__2);
l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__3);
l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarId___lambda__1___closed__4);
l_Lean_Elab_Tactic_getFVarIds___boxed__const__1 = _init_l_Lean_Elab_Tactic_getFVarIds___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarIds___boxed__const__1);
l_Lean_Elab_Tactic_evalApply___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_evalApply___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___lambda__1___closed__1);
l_Lean_Elab_Tactic_evalApply___closed__1 = _init_l_Lean_Elab_Tactic_evalApply___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___closed__1);
l_Lean_Elab_Tactic_evalApply___closed__2 = _init_l_Lean_Elab_Tactic_evalApply___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___closed__2);
l_Lean_Elab_Tactic_evalApply___closed__3 = _init_l_Lean_Elab_Tactic_evalApply___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalApply___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApply__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalApply__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalApply_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalConstructor___rarg___closed__1 = _init_l_Lean_Elab_Tactic_evalConstructor___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalConstructor___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalConstructor__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalConstructor_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalWithReducible_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalWithReducibleAndInstances_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalWithUnfoldingAll_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__1);
l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabAsFVar___lambda__1___closed__2);
l_Lean_Elab_Tactic_evalRename___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_evalRename___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___lambda__1___closed__1);
l_Lean_Elab_Tactic_evalRename___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_evalRename___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___lambda__1___closed__2);
l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___lambda__1___closed__3);
l_Lean_Elab_Tactic_evalRename___closed__1 = _init_l_Lean_Elab_Tactic_evalRename___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___closed__1);
l_Lean_Elab_Tactic_evalRename___closed__2 = _init_l_Lean_Elab_Tactic_evalRename___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___closed__2);
l_Lean_Elab_Tactic_evalRename___closed__3 = _init_l_Lean_Elab_Tactic_evalRename___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___closed__3);
l_Lean_Elab_Tactic_evalRename___closed__4 = _init_l_Lean_Elab_Tactic_evalRename___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRename___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRename__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRename__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalRename_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__3 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__3);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__4 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__2___closed__4);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___lambda__3___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__2 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__2);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__3 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__3);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__4 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__4);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__5);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__6 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__6();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__6);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__7 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__7();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___spec__1___closed__7);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___lambda__2___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__3 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__3);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__4 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__4);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__5 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__5);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__6 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__6);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__7 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__7);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__8 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__1___closed__8);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___lambda__2___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__1 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__1);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__2 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__2);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__3 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__3);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__4 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__4);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__5 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__5);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__6 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__6);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__7 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__7);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__8 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__8);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__9 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__9);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__10 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__10);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__11 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__11);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__12 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__12);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__13 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__13);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__14 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__14);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__15 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__15);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__16 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__16);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__17 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__17);
l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__18 = _init_l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Tactic_ElabTerm_0__Lean_Elab_Tactic_elabNativeDecideCoreUnsafe___closed__18);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__1);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__2);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__3);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__4);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__5 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__2___closed__5);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__1);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__3___closed__2);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__1);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__2);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__3);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__4 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__4);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__5 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__5);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__6 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__6);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__7);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__8 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__8);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__9 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__9);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__10 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__10);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__11 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__11);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__12 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__12);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__13 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__13);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__14 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__14);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__15 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__15);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__16 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__16);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__17 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__17);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__18 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__18);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__19 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__19);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__20 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__20);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__21 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__21();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__21);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__22 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__22();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__22);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__23 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__23();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__23);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__24 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__24();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__24);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__25 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__25();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__25);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__26 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__26();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__26);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__27 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__27();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__27);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__28 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__28();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__28);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__29 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__29();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__29);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__30 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__30();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__30);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__31 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__31();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__31);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__32 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__32();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__32);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__33 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__33();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__33);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__34 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__34();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__34);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__35 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__35();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__35);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__36 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__36();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__36);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__37 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__37();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__37);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__38 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__38();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__38);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__39 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__39();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__39);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__40 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__40();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__40);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__41 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__41();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__41);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__42 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__42();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__42);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__43 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__43();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__43);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__44 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__44();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__44);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__45 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__45();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__45);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__46 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__46();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__46);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__47 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__47();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__47);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__48 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__48();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__48);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__49 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__49();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__49);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__50 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__50();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__50);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__51 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__51();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__51);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__52 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__52();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__52);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__53 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__53();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__53);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__54 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__54();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__54);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__55 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__55();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__55);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__56 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__56();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__56);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__57 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__57();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__57);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__58 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__58();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__58);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__59 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__59();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__59);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__60 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__60();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__60);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__61 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__61();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__61);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__62 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__62();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__62);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__63 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__63();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__63);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__64 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__64();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__64);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__65 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__65();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__65);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__66 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__66();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__66);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__67 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__67();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__67);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__68 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__68();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__68);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__69 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__69();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__69);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__70 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__70();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__70);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__71 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__71();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__71);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__72 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__72();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__72);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__73 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__73();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__73);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__74 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__74();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__74);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__75 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__75();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__75);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__76 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__76();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__76);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__77 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__77();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__77);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__78 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__78();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__78);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__79 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__79();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__4___closed__79);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__1 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__1);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__2 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__2);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__3 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__3);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__4 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__4);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__5 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__5);
l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__6 = _init_l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore_diagnose___lambda__5___closed__6);
l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__1);
l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore___lambda__2___closed__2);
l_Lean_Elab_Tactic_evalDecideCore___closed__1 = _init_l_Lean_Elab_Tactic_evalDecideCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideCore___closed__1);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__1 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__1);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__2 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_ElabTerm___hyg_6163____closed__2);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__1);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__2);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__3);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__1___closed__4);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__1);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__2___closed__2);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__3___closed__1);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__1);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__2);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__3);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__4 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__4);
l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__5 = _init_l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_elabDecideConfig___lambda__4___closed__5);
l_Lean_Elab_Tactic_evalDecide___closed__1 = _init_l_Lean_Elab_Tactic_evalDecide___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___closed__1);
l_Lean_Elab_Tactic_evalDecide___closed__2 = _init_l_Lean_Elab_Tactic_evalDecide___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecide___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDecide__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalDecideBang___closed__1 = _init_l_Lean_Elab_Tactic_evalDecideBang___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideBang___closed__1);
l_Lean_Elab_Tactic_evalDecideBang___closed__2 = _init_l_Lean_Elab_Tactic_evalDecideBang___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDecideBang___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDecideBang__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalNativeDecide___closed__1 = _init_l_Lean_Elab_Tactic_evalNativeDecide___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___closed__1);
l_Lean_Elab_Tactic_evalNativeDecide___closed__2 = _init_l_Lean_Elab_Tactic_evalNativeDecide___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalNativeDecide___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
