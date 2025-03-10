// Lean compiler output
// Module: Lean.Elab.SyntheticMVars
// Imports: Lean.Meta.Tactic.Util Lean.Util.NumObjs Lean.Util.ForEachExpr Lean.Util.OccursCheck Lean.Elab.Tactic.Basic
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
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_instBEqPostponeBehavior___closed__1;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__13;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_runTactic___lambda__6___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__12;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__7;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__15;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__20;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__18;
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Term_runTactic___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_instInhabitedPostponeBehavior;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__2;
lean_object* l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_sharecommon_quick(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__5;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2;
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_Elab_Term_runTactic___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__6;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__3;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_toCtorIdx___boxed(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2;
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__3;
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instReprPostponeBehavior;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__2;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
static lean_object* l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__1;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__5;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instMonadTermElabM;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__3;
static lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_withoutRecover___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__22;
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Term_runTactic___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__6;
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__8;
static lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__5;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__5;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__14;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__18;
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedLocalContext;
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__2;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__7;
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__19;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_runTactic___lambda__6___closed__2;
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__19;
static lean_object* l_Lean_Elab_Term_runTactic___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseContraints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__12;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Term_withSavedContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponing___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___closed__1;
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158_(uint8_t, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__14;
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runPendingTacticsAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__17___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__8___boxed(lean_object**);
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__15;
static lean_object* l_Lean_Elab_Term_instReprPostponeBehavior___closed__1;
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3;
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Elab_Term_runTactic___lambda__6___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedPostponedEntry;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__1;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115_(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_traceAtCmdPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1;
lean_object* l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__15;
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__4___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___lambda__1(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedDefaultInstances;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at_Lean_Elab_Term_runTactic___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
extern lean_object* l_Lean_Meta_defaultInstanceExtension;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__5;
static lean_object* l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_ofBool___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__18;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseContraints___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__2;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__4;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_Elab_Term_runTactic___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__8;
lean_object* l_Lean_MetavarContext_getExprAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__9;
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize(lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__1(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__7;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__5;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Term_runTactic___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__7;
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeSomeUsingDefault_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Term_withDeclName___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_cancelRec___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_coerce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery(lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__21;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__4;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__4;
lean_object* l_Lean_getDelayedMVarRoot___at_Lean_Elab_Term_isLetRecAuxMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__2;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runTactic___spec__22(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_Term_runTactic___spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6___closed__1;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__3;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__11;
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___closed__1;
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_postponeExceptionId;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__17;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_LocalContext_mkAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__3;
lean_object* l_Lean_PersistentArray_get_x21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasMissing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__1;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__3;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__10;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__12;
lean_object* l_Lean_logAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__8(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3;
static uint64_t l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_Level_instHashable;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__17;
lean_object* l_Lean_Elab_Term_extraMsgToMsg(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__16;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__20;
lean_object* l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__8;
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_runTactic___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instBEqPostponeBehavior;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_instBEq;
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__10;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1;
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1;
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__14;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__7;
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__16;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_normLtAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_getPostponed___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__6;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runTactic___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at_Lean_Elab_Term_runTactic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__1;
size_t lean_usize_land(size_t, size_t);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__11;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__9;
lean_object* l_Lean_Meta_processPostponed(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*7 + 1, x_13);
x_14 = 1;
x_15 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_19 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 2);
x_20 = lean_ctor_get(x_4, 2);
x_21 = lean_ctor_get(x_4, 3);
x_22 = lean_ctor_get(x_4, 4);
x_23 = lean_ctor_get(x_4, 5);
x_24 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 3);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 4);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 5);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 6);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 7);
x_29 = lean_ctor_get(x_4, 6);
x_30 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_31 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_32 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_inc(x_29);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_33 = 0;
x_34 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_17);
lean_ctor_set(x_34, 2, x_20);
lean_ctor_set(x_34, 3, x_21);
lean_ctor_set(x_34, 4, x_22);
lean_ctor_set(x_34, 5, x_23);
lean_ctor_set(x_34, 6, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*7, x_18);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 2, x_19);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 3, x_24);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 4, x_25);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 5, x_26);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 6, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 7, x_28);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 8, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 9, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 10, x_32);
x_35 = 1;
x_36 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_33, x_35, x_34, x_5, x_6, x_7, x_8, x_9, x_10);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_4);
if (x_37 == 0)
{
uint8_t x_38; uint8_t x_39; lean_object* x_40; 
lean_ctor_set_uint8(x_4, sizeof(void*)*7 + 1, x_3);
x_38 = 0;
x_39 = 1;
x_40 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_38, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*7);
x_44 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 2);
x_45 = lean_ctor_get(x_4, 2);
x_46 = lean_ctor_get(x_4, 3);
x_47 = lean_ctor_get(x_4, 4);
x_48 = lean_ctor_get(x_4, 5);
x_49 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 3);
x_50 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 4);
x_51 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 5);
x_52 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 6);
x_53 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 7);
x_54 = lean_ctor_get(x_4, 6);
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_56 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_57 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
lean_inc(x_54);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_4);
x_58 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set(x_58, 2, x_45);
lean_ctor_set(x_58, 3, x_46);
lean_ctor_set(x_58, 4, x_47);
lean_ctor_set(x_58, 5, x_48);
lean_ctor_set(x_58, 6, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*7, x_43);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 1, x_3);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 2, x_44);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 3, x_49);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 4, x_50);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 5, x_51);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 6, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 7, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 8, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 9, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 10, x_57);
x_59 = 0;
x_60 = 1;
x_61 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_59, x_60, x_58, x_5, x_6, x_7, x_8, x_9, x_10);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_13, x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
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
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_MetavarContext_getExprAssignmentCore_x3f(x_19, x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_13, x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
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
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(x_19, x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
static lean_object* _init_l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_name_eq(x_1, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_getDelayedMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__5(x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 0);
lean_dec(x_25);
x_26 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
lean_ctor_set(x_19, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_32 = x_19;
} else {
 lean_dec_ref(x_19);
 x_32 = lean_box(0);
}
x_33 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_dec(x_18);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_dec(x_19);
x_38 = lean_ctor_get(x_21, 0);
lean_inc(x_38);
lean_dec(x_21);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_2 = x_39;
x_3 = x_37;
x_10 = x_36;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_dec(x_12);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_dec(x_13);
x_43 = lean_ctor_get(x_15, 0);
lean_inc(x_43);
lean_dec(x_15);
x_44 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_43, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
x_45 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__2;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_10);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasExprMVar(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
x_18 = l_Lean_Expr_hash(x_2);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
x_29 = lean_usize_land(x_25, x_28);
x_30 = lean_array_uget(x_16, x_29);
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_CollectLevelMVars_visitExpr___spec__1(x_2, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_33 = lean_ctor_get(x_3, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_15, x_35);
lean_dec(x_15);
x_37 = lean_box(0);
lean_inc(x_2);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_30);
x_39 = lean_array_uset(x_16, x_29, x_38);
x_40 = lean_unsigned_to_nat(4u);
x_41 = lean_nat_mul(x_36, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(x_39);
lean_ctor_set(x_3, 1, x_46);
lean_ctor_set(x_3, 0, x_36);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
lean_dec(x_2);
x_48 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3(x_1, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_48;
}
case 5:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
lean_dec(x_2);
x_51 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_49, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
lean_dec(x_50);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_52, 0);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_52, 0, x_60);
return x_51;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_dec(x_52);
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_63 = x_53;
} else {
 lean_dec_ref(x_53);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_51, 0, x_65);
return x_51;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
lean_dec(x_51);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_68 = x_52;
} else {
 lean_dec_ref(x_52);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_53, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_70 = x_53;
} else {
 lean_dec_ref(x_53);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_53);
x_74 = lean_ctor_get(x_51, 1);
lean_inc(x_74);
lean_dec(x_51);
x_75 = lean_ctor_get(x_52, 1);
lean_inc(x_75);
lean_dec(x_52);
x_2 = x_50;
x_3 = x_75;
x_10 = x_74;
goto _start;
}
}
case 6:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
lean_dec(x_2);
x_79 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
lean_dec(x_78);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_79, 0);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_80, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_81);
if (x_86 == 0)
{
return x_79;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_80, 0, x_88);
return x_79;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
lean_dec(x_80);
x_90 = lean_ctor_get(x_81, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_91 = x_81;
} else {
 lean_dec_ref(x_81);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
lean_ctor_set(x_79, 0, x_93);
return x_79;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_79, 1);
lean_inc(x_94);
lean_dec(x_79);
x_95 = lean_ctor_get(x_80, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_96 = x_80;
} else {
 lean_dec_ref(x_80);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_81, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_98 = x_81;
} else {
 lean_dec_ref(x_81);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_95);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_94);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_81);
x_102 = lean_ctor_get(x_79, 1);
lean_inc(x_102);
lean_dec(x_79);
x_103 = lean_ctor_get(x_80, 1);
lean_inc(x_103);
lean_dec(x_80);
x_2 = x_78;
x_3 = x_103;
x_10 = x_102;
goto _start;
}
}
case 7:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_2, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_2, 2);
lean_inc(x_106);
lean_dec(x_2);
x_107 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_105, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
lean_dec(x_106);
x_110 = !lean_is_exclusive(x_107);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_107, 0);
lean_dec(x_111);
x_112 = !lean_is_exclusive(x_108);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_108, 0);
lean_dec(x_113);
x_114 = !lean_is_exclusive(x_109);
if (x_114 == 0)
{
return x_107;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_108, 0, x_116);
return x_107;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_108, 1);
lean_inc(x_117);
lean_dec(x_108);
x_118 = lean_ctor_get(x_109, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_119 = x_109;
} else {
 lean_dec_ref(x_109);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_117);
lean_ctor_set(x_107, 0, x_121);
return x_107;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_ctor_get(x_107, 1);
lean_inc(x_122);
lean_dec(x_107);
x_123 = lean_ctor_get(x_108, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_124 = x_108;
} else {
 lean_dec_ref(x_108);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_109, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_126 = x_109;
} else {
 lean_dec_ref(x_109);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
if (lean_is_scalar(x_124)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_124;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_123);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_122);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_109);
x_130 = lean_ctor_get(x_107, 1);
lean_inc(x_130);
lean_dec(x_107);
x_131 = lean_ctor_get(x_108, 1);
lean_inc(x_131);
lean_dec(x_108);
x_2 = x_106;
x_3 = x_131;
x_10 = x_130;
goto _start;
}
}
case 8:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_ctor_get(x_2, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_2, 2);
lean_inc(x_134);
x_135 = lean_ctor_get(x_2, 3);
lean_inc(x_135);
lean_dec(x_2);
x_136 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_133, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
lean_dec(x_135);
lean_dec(x_134);
x_139 = !lean_is_exclusive(x_136);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_136, 0);
lean_dec(x_140);
x_141 = !lean_is_exclusive(x_137);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_137, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_138);
if (x_143 == 0)
{
return x_136;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
lean_dec(x_138);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_137, 0, x_145);
return x_136;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_137, 1);
lean_inc(x_146);
lean_dec(x_137);
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_148 = x_138;
} else {
 lean_dec_ref(x_138);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 1, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_147);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_146);
lean_ctor_set(x_136, 0, x_150);
return x_136;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_151 = lean_ctor_get(x_136, 1);
lean_inc(x_151);
lean_dec(x_136);
x_152 = lean_ctor_get(x_137, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_153 = x_137;
} else {
 lean_dec_ref(x_137);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_138, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_155 = x_138;
} else {
 lean_dec_ref(x_138);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 1, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_151);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_138);
x_159 = lean_ctor_get(x_136, 1);
lean_inc(x_159);
lean_dec(x_136);
x_160 = lean_ctor_get(x_137, 1);
lean_inc(x_160);
lean_dec(x_137);
x_161 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_134, x_160, x_4, x_5, x_6, x_7, x_8, x_9, x_159);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
lean_dec(x_135);
x_164 = !lean_is_exclusive(x_161);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_161, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_162);
if (x_166 == 0)
{
lean_object* x_167; uint8_t x_168; 
x_167 = lean_ctor_get(x_162, 0);
lean_dec(x_167);
x_168 = !lean_is_exclusive(x_163);
if (x_168 == 0)
{
return x_161;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_163, 0);
lean_inc(x_169);
lean_dec(x_163);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_162, 0, x_170);
return x_161;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_162, 1);
lean_inc(x_171);
lean_dec(x_162);
x_172 = lean_ctor_get(x_163, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_173 = x_163;
} else {
 lean_dec_ref(x_163);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 1, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_172);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_171);
lean_ctor_set(x_161, 0, x_175);
return x_161;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_176 = lean_ctor_get(x_161, 1);
lean_inc(x_176);
lean_dec(x_161);
x_177 = lean_ctor_get(x_162, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_178 = x_162;
} else {
 lean_dec_ref(x_162);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_163, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_180 = x_163;
} else {
 lean_dec_ref(x_163);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
if (lean_is_scalar(x_178)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_178;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_177);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_176);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_163);
x_184 = lean_ctor_get(x_161, 1);
lean_inc(x_184);
lean_dec(x_161);
x_185 = lean_ctor_get(x_162, 1);
lean_inc(x_185);
lean_dec(x_162);
x_2 = x_135;
x_3 = x_185;
x_10 = x_184;
goto _start;
}
}
}
case 10:
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_2, 1);
lean_inc(x_187);
lean_dec(x_2);
x_2 = x_187;
goto _start;
}
case 11:
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_2, 2);
lean_inc(x_189);
lean_dec(x_2);
x_2 = x_189;
goto _start;
}
default: 
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_2);
x_191 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_3);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_10);
return x_193;
}
}
}
else
{
lean_ctor_set(x_3, 1, x_39);
lean_ctor_set(x_3, 0, x_36);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_2, 0);
lean_inc(x_194);
lean_dec(x_2);
x_195 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3(x_1, x_194, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_195;
}
case 5:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_2, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_2, 1);
lean_inc(x_197);
lean_dec(x_2);
x_198 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_196, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
lean_dec(x_197);
x_201 = !lean_is_exclusive(x_198);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_198, 0);
lean_dec(x_202);
x_203 = !lean_is_exclusive(x_199);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_199, 0);
lean_dec(x_204);
x_205 = !lean_is_exclusive(x_200);
if (x_205 == 0)
{
return x_198;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
lean_dec(x_200);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_199, 0, x_207);
return x_198;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_199, 1);
lean_inc(x_208);
lean_dec(x_199);
x_209 = lean_ctor_get(x_200, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_210 = x_200;
} else {
 lean_dec_ref(x_200);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 1, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_209);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_208);
lean_ctor_set(x_198, 0, x_212);
return x_198;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_213 = lean_ctor_get(x_198, 1);
lean_inc(x_213);
lean_dec(x_198);
x_214 = lean_ctor_get(x_199, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_215 = x_199;
} else {
 lean_dec_ref(x_199);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_200, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_217 = x_200;
} else {
 lean_dec_ref(x_200);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(0, 1, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_216);
if (lean_is_scalar(x_215)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_215;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_214);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_213);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_200);
x_221 = lean_ctor_get(x_198, 1);
lean_inc(x_221);
lean_dec(x_198);
x_222 = lean_ctor_get(x_199, 1);
lean_inc(x_222);
lean_dec(x_199);
x_2 = x_197;
x_3 = x_222;
x_10 = x_221;
goto _start;
}
}
case 6:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_224 = lean_ctor_get(x_2, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_2, 2);
lean_inc(x_225);
lean_dec(x_2);
x_226 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_224, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
if (lean_obj_tag(x_228) == 0)
{
uint8_t x_229; 
lean_dec(x_225);
x_229 = !lean_is_exclusive(x_226);
if (x_229 == 0)
{
lean_object* x_230; uint8_t x_231; 
x_230 = lean_ctor_get(x_226, 0);
lean_dec(x_230);
x_231 = !lean_is_exclusive(x_227);
if (x_231 == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_227, 0);
lean_dec(x_232);
x_233 = !lean_is_exclusive(x_228);
if (x_233 == 0)
{
return x_226;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_228, 0);
lean_inc(x_234);
lean_dec(x_228);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_227, 0, x_235);
return x_226;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_ctor_get(x_227, 1);
lean_inc(x_236);
lean_dec(x_227);
x_237 = lean_ctor_get(x_228, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_238 = x_228;
} else {
 lean_dec_ref(x_228);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 1, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_237);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_236);
lean_ctor_set(x_226, 0, x_240);
return x_226;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_241 = lean_ctor_get(x_226, 1);
lean_inc(x_241);
lean_dec(x_226);
x_242 = lean_ctor_get(x_227, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_243 = x_227;
} else {
 lean_dec_ref(x_227);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_228, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_245 = x_228;
} else {
 lean_dec_ref(x_228);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 1, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_244);
if (lean_is_scalar(x_243)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_243;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_242);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_241);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_228);
x_249 = lean_ctor_get(x_226, 1);
lean_inc(x_249);
lean_dec(x_226);
x_250 = lean_ctor_get(x_227, 1);
lean_inc(x_250);
lean_dec(x_227);
x_2 = x_225;
x_3 = x_250;
x_10 = x_249;
goto _start;
}
}
case 7:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_2, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_2, 2);
lean_inc(x_253);
lean_dec(x_2);
x_254 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_252, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
uint8_t x_257; 
lean_dec(x_253);
x_257 = !lean_is_exclusive(x_254);
if (x_257 == 0)
{
lean_object* x_258; uint8_t x_259; 
x_258 = lean_ctor_get(x_254, 0);
lean_dec(x_258);
x_259 = !lean_is_exclusive(x_255);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_255, 0);
lean_dec(x_260);
x_261 = !lean_is_exclusive(x_256);
if (x_261 == 0)
{
return x_254;
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_256, 0);
lean_inc(x_262);
lean_dec(x_256);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_255, 0, x_263);
return x_254;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_264 = lean_ctor_get(x_255, 1);
lean_inc(x_264);
lean_dec(x_255);
x_265 = lean_ctor_get(x_256, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_266 = x_256;
} else {
 lean_dec_ref(x_256);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(0, 1, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_265);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_264);
lean_ctor_set(x_254, 0, x_268);
return x_254;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_269 = lean_ctor_get(x_254, 1);
lean_inc(x_269);
lean_dec(x_254);
x_270 = lean_ctor_get(x_255, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_271 = x_255;
} else {
 lean_dec_ref(x_255);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_256, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 x_273 = x_256;
} else {
 lean_dec_ref(x_256);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 1, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_272);
if (lean_is_scalar(x_271)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_271;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_270);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_269);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_256);
x_277 = lean_ctor_get(x_254, 1);
lean_inc(x_277);
lean_dec(x_254);
x_278 = lean_ctor_get(x_255, 1);
lean_inc(x_278);
lean_dec(x_255);
x_2 = x_253;
x_3 = x_278;
x_10 = x_277;
goto _start;
}
}
case 8:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_280 = lean_ctor_get(x_2, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_2, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_2, 3);
lean_inc(x_282);
lean_dec(x_2);
x_283 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_280, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
uint8_t x_286; 
lean_dec(x_282);
lean_dec(x_281);
x_286 = !lean_is_exclusive(x_283);
if (x_286 == 0)
{
lean_object* x_287; uint8_t x_288; 
x_287 = lean_ctor_get(x_283, 0);
lean_dec(x_287);
x_288 = !lean_is_exclusive(x_284);
if (x_288 == 0)
{
lean_object* x_289; uint8_t x_290; 
x_289 = lean_ctor_get(x_284, 0);
lean_dec(x_289);
x_290 = !lean_is_exclusive(x_285);
if (x_290 == 0)
{
return x_283;
}
else
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_285, 0);
lean_inc(x_291);
lean_dec(x_285);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_284, 0, x_292);
return x_283;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_284, 1);
lean_inc(x_293);
lean_dec(x_284);
x_294 = lean_ctor_get(x_285, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_295 = x_285;
} else {
 lean_dec_ref(x_285);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(0, 1, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_294);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_293);
lean_ctor_set(x_283, 0, x_297);
return x_283;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_298 = lean_ctor_get(x_283, 1);
lean_inc(x_298);
lean_dec(x_283);
x_299 = lean_ctor_get(x_284, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_300 = x_284;
} else {
 lean_dec_ref(x_284);
 x_300 = lean_box(0);
}
x_301 = lean_ctor_get(x_285, 0);
lean_inc(x_301);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_302 = x_285;
} else {
 lean_dec_ref(x_285);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 1, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_301);
if (lean_is_scalar(x_300)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_300;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_299);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_298);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_285);
x_306 = lean_ctor_get(x_283, 1);
lean_inc(x_306);
lean_dec(x_283);
x_307 = lean_ctor_get(x_284, 1);
lean_inc(x_307);
lean_dec(x_284);
x_308 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_281, x_307, x_4, x_5, x_6, x_7, x_8, x_9, x_306);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
if (lean_obj_tag(x_310) == 0)
{
uint8_t x_311; 
lean_dec(x_282);
x_311 = !lean_is_exclusive(x_308);
if (x_311 == 0)
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_308, 0);
lean_dec(x_312);
x_313 = !lean_is_exclusive(x_309);
if (x_313 == 0)
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_309, 0);
lean_dec(x_314);
x_315 = !lean_is_exclusive(x_310);
if (x_315 == 0)
{
return x_308;
}
else
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_310, 0);
lean_inc(x_316);
lean_dec(x_310);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_309, 0, x_317);
return x_308;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_318 = lean_ctor_get(x_309, 1);
lean_inc(x_318);
lean_dec(x_309);
x_319 = lean_ctor_get(x_310, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_320 = x_310;
} else {
 lean_dec_ref(x_310);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(0, 1, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_319);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_318);
lean_ctor_set(x_308, 0, x_322);
return x_308;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_323 = lean_ctor_get(x_308, 1);
lean_inc(x_323);
lean_dec(x_308);
x_324 = lean_ctor_get(x_309, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 x_325 = x_309;
} else {
 lean_dec_ref(x_309);
 x_325 = lean_box(0);
}
x_326 = lean_ctor_get(x_310, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_327 = x_310;
} else {
 lean_dec_ref(x_310);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(0, 1, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_326);
if (lean_is_scalar(x_325)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_325;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_324);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_323);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_310);
x_331 = lean_ctor_get(x_308, 1);
lean_inc(x_331);
lean_dec(x_308);
x_332 = lean_ctor_get(x_309, 1);
lean_inc(x_332);
lean_dec(x_309);
x_2 = x_282;
x_3 = x_332;
x_10 = x_331;
goto _start;
}
}
}
case 10:
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_2, 1);
lean_inc(x_334);
lean_dec(x_2);
x_2 = x_334;
goto _start;
}
case 11:
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_2, 2);
lean_inc(x_336);
lean_dec(x_2);
x_2 = x_336;
goto _start;
}
default: 
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_2);
x_338 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_3);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_10);
return x_340;
}
}
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
lean_dec(x_3);
x_341 = lean_unsigned_to_nat(1u);
x_342 = lean_nat_add(x_15, x_341);
lean_dec(x_15);
x_343 = lean_box(0);
lean_inc(x_2);
x_344 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_344, 0, x_2);
lean_ctor_set(x_344, 1, x_343);
lean_ctor_set(x_344, 2, x_30);
x_345 = lean_array_uset(x_16, x_29, x_344);
x_346 = lean_unsigned_to_nat(4u);
x_347 = lean_nat_mul(x_342, x_346);
x_348 = lean_unsigned_to_nat(3u);
x_349 = lean_nat_div(x_347, x_348);
lean_dec(x_347);
x_350 = lean_array_get_size(x_345);
x_351 = lean_nat_dec_le(x_349, x_350);
lean_dec(x_350);
lean_dec(x_349);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; 
x_352 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_CollectLevelMVars_visitExpr___spec__2(x_345);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_342);
lean_ctor_set(x_353, 1, x_352);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_2, 0);
lean_inc(x_354);
lean_dec(x_2);
x_355 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3(x_1, x_354, x_353, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_355;
}
case 5:
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_356 = lean_ctor_get(x_2, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_2, 1);
lean_inc(x_357);
lean_dec(x_2);
x_358 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_356, x_353, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_357);
x_361 = lean_ctor_get(x_358, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_362 = x_358;
} else {
 lean_dec_ref(x_358);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_359, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_364 = x_359;
} else {
 lean_dec_ref(x_359);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_360, 0);
lean_inc(x_365);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 x_366 = x_360;
} else {
 lean_dec_ref(x_360);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(0, 1, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_365);
if (lean_is_scalar(x_364)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_364;
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_363);
if (lean_is_scalar(x_362)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_362;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_361);
return x_369;
}
else
{
lean_object* x_370; lean_object* x_371; 
lean_dec(x_360);
x_370 = lean_ctor_get(x_358, 1);
lean_inc(x_370);
lean_dec(x_358);
x_371 = lean_ctor_get(x_359, 1);
lean_inc(x_371);
lean_dec(x_359);
x_2 = x_357;
x_3 = x_371;
x_10 = x_370;
goto _start;
}
}
case 6:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_373 = lean_ctor_get(x_2, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_2, 2);
lean_inc(x_374);
lean_dec(x_2);
x_375 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_373, x_353, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_374);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_379 = x_375;
} else {
 lean_dec_ref(x_375);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_376, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_381 = x_376;
} else {
 lean_dec_ref(x_376);
 x_381 = lean_box(0);
}
x_382 = lean_ctor_get(x_377, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_383 = x_377;
} else {
 lean_dec_ref(x_377);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(0, 1, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_382);
if (lean_is_scalar(x_381)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_381;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_380);
if (lean_is_scalar(x_379)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_379;
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_378);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_377);
x_387 = lean_ctor_get(x_375, 1);
lean_inc(x_387);
lean_dec(x_375);
x_388 = lean_ctor_get(x_376, 1);
lean_inc(x_388);
lean_dec(x_376);
x_2 = x_374;
x_3 = x_388;
x_10 = x_387;
goto _start;
}
}
case 7:
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_390 = lean_ctor_get(x_2, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_2, 2);
lean_inc(x_391);
lean_dec(x_2);
x_392 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_390, x_353, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_391);
x_395 = lean_ctor_get(x_392, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_396 = x_392;
} else {
 lean_dec_ref(x_392);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_393, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_398 = x_393;
} else {
 lean_dec_ref(x_393);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_394, 0);
lean_inc(x_399);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 x_400 = x_394;
} else {
 lean_dec_ref(x_394);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(0, 1, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_399);
if (lean_is_scalar(x_398)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_398;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_397);
if (lean_is_scalar(x_396)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_396;
}
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_395);
return x_403;
}
else
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_394);
x_404 = lean_ctor_get(x_392, 1);
lean_inc(x_404);
lean_dec(x_392);
x_405 = lean_ctor_get(x_393, 1);
lean_inc(x_405);
lean_dec(x_393);
x_2 = x_391;
x_3 = x_405;
x_10 = x_404;
goto _start;
}
}
case 8:
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_407 = lean_ctor_get(x_2, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_2, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_2, 3);
lean_inc(x_409);
lean_dec(x_2);
x_410 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_407, x_353, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_409);
lean_dec(x_408);
x_413 = lean_ctor_get(x_410, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_414 = x_410;
} else {
 lean_dec_ref(x_410);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_411, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_416 = x_411;
} else {
 lean_dec_ref(x_411);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_412, 0);
lean_inc(x_417);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 x_418 = x_412;
} else {
 lean_dec_ref(x_412);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(0, 1, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_417);
if (lean_is_scalar(x_416)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_416;
}
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_415);
if (lean_is_scalar(x_414)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_414;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_413);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_412);
x_422 = lean_ctor_get(x_410, 1);
lean_inc(x_422);
lean_dec(x_410);
x_423 = lean_ctor_get(x_411, 1);
lean_inc(x_423);
lean_dec(x_411);
x_424 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_408, x_423, x_4, x_5, x_6, x_7, x_8, x_9, x_422);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_409);
x_427 = lean_ctor_get(x_424, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_428 = x_424;
} else {
 lean_dec_ref(x_424);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_425, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_430 = x_425;
} else {
 lean_dec_ref(x_425);
 x_430 = lean_box(0);
}
x_431 = lean_ctor_get(x_426, 0);
lean_inc(x_431);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_432 = x_426;
} else {
 lean_dec_ref(x_426);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(0, 1, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_431);
if (lean_is_scalar(x_430)) {
 x_434 = lean_alloc_ctor(0, 2, 0);
} else {
 x_434 = x_430;
}
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_429);
if (lean_is_scalar(x_428)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_428;
}
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_427);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_426);
x_436 = lean_ctor_get(x_424, 1);
lean_inc(x_436);
lean_dec(x_424);
x_437 = lean_ctor_get(x_425, 1);
lean_inc(x_437);
lean_dec(x_425);
x_2 = x_409;
x_3 = x_437;
x_10 = x_436;
goto _start;
}
}
}
case 10:
{
lean_object* x_439; 
x_439 = lean_ctor_get(x_2, 1);
lean_inc(x_439);
lean_dec(x_2);
x_2 = x_439;
x_3 = x_353;
goto _start;
}
case 11:
{
lean_object* x_441; 
x_441 = lean_ctor_get(x_2, 2);
lean_inc(x_441);
lean_dec(x_2);
x_2 = x_441;
x_3 = x_353;
goto _start;
}
default: 
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_2);
x_443 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_353);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_10);
return x_445;
}
}
}
else
{
lean_object* x_446; 
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_342);
lean_ctor_set(x_446, 1, x_345);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_2, 0);
lean_inc(x_447);
lean_dec(x_2);
x_448 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3(x_1, x_447, x_446, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_448;
}
case 5:
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_449 = lean_ctor_get(x_2, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_2, 1);
lean_inc(x_450);
lean_dec(x_2);
x_451 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_449, x_446, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_450);
x_454 = lean_ctor_get(x_451, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_455 = x_451;
} else {
 lean_dec_ref(x_451);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_452, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_457 = x_452;
} else {
 lean_dec_ref(x_452);
 x_457 = lean_box(0);
}
x_458 = lean_ctor_get(x_453, 0);
lean_inc(x_458);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 x_459 = x_453;
} else {
 lean_dec_ref(x_453);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 1, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_458);
if (lean_is_scalar(x_457)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_457;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_456);
if (lean_is_scalar(x_455)) {
 x_462 = lean_alloc_ctor(0, 2, 0);
} else {
 x_462 = x_455;
}
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_454);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_453);
x_463 = lean_ctor_get(x_451, 1);
lean_inc(x_463);
lean_dec(x_451);
x_464 = lean_ctor_get(x_452, 1);
lean_inc(x_464);
lean_dec(x_452);
x_2 = x_450;
x_3 = x_464;
x_10 = x_463;
goto _start;
}
}
case 6:
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = lean_ctor_get(x_2, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_2, 2);
lean_inc(x_467);
lean_dec(x_2);
x_468 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_466, x_446, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_467);
x_471 = lean_ctor_get(x_468, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_472 = x_468;
} else {
 lean_dec_ref(x_468);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_469, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_474 = x_469;
} else {
 lean_dec_ref(x_469);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_470, 0);
lean_inc(x_475);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 x_476 = x_470;
} else {
 lean_dec_ref(x_470);
 x_476 = lean_box(0);
}
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(0, 1, 0);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_475);
if (lean_is_scalar(x_474)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_474;
}
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_473);
if (lean_is_scalar(x_472)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_472;
}
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_471);
return x_479;
}
else
{
lean_object* x_480; lean_object* x_481; 
lean_dec(x_470);
x_480 = lean_ctor_get(x_468, 1);
lean_inc(x_480);
lean_dec(x_468);
x_481 = lean_ctor_get(x_469, 1);
lean_inc(x_481);
lean_dec(x_469);
x_2 = x_467;
x_3 = x_481;
x_10 = x_480;
goto _start;
}
}
case 7:
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_483 = lean_ctor_get(x_2, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_2, 2);
lean_inc(x_484);
lean_dec(x_2);
x_485 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_483, x_446, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_484);
x_488 = lean_ctor_get(x_485, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_489 = x_485;
} else {
 lean_dec_ref(x_485);
 x_489 = lean_box(0);
}
x_490 = lean_ctor_get(x_486, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_491 = x_486;
} else {
 lean_dec_ref(x_486);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_487, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 x_493 = x_487;
} else {
 lean_dec_ref(x_487);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(0, 1, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_492);
if (lean_is_scalar(x_491)) {
 x_495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_495 = x_491;
}
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_490);
if (lean_is_scalar(x_489)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_489;
}
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_488);
return x_496;
}
else
{
lean_object* x_497; lean_object* x_498; 
lean_dec(x_487);
x_497 = lean_ctor_get(x_485, 1);
lean_inc(x_497);
lean_dec(x_485);
x_498 = lean_ctor_get(x_486, 1);
lean_inc(x_498);
lean_dec(x_486);
x_2 = x_484;
x_3 = x_498;
x_10 = x_497;
goto _start;
}
}
case 8:
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_500 = lean_ctor_get(x_2, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_2, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_2, 3);
lean_inc(x_502);
lean_dec(x_2);
x_503 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_500, x_446, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_502);
lean_dec(x_501);
x_506 = lean_ctor_get(x_503, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_507 = x_503;
} else {
 lean_dec_ref(x_503);
 x_507 = lean_box(0);
}
x_508 = lean_ctor_get(x_504, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 x_509 = x_504;
} else {
 lean_dec_ref(x_504);
 x_509 = lean_box(0);
}
x_510 = lean_ctor_get(x_505, 0);
lean_inc(x_510);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 x_511 = x_505;
} else {
 lean_dec_ref(x_505);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(0, 1, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_510);
if (lean_is_scalar(x_509)) {
 x_513 = lean_alloc_ctor(0, 2, 0);
} else {
 x_513 = x_509;
}
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_508);
if (lean_is_scalar(x_507)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_507;
}
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_506);
return x_514;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_505);
x_515 = lean_ctor_get(x_503, 1);
lean_inc(x_515);
lean_dec(x_503);
x_516 = lean_ctor_get(x_504, 1);
lean_inc(x_516);
lean_dec(x_504);
x_517 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_501, x_516, x_4, x_5, x_6, x_7, x_8, x_9, x_515);
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_502);
x_520 = lean_ctor_get(x_517, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 lean_ctor_release(x_517, 1);
 x_521 = x_517;
} else {
 lean_dec_ref(x_517);
 x_521 = lean_box(0);
}
x_522 = lean_ctor_get(x_518, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_523 = x_518;
} else {
 lean_dec_ref(x_518);
 x_523 = lean_box(0);
}
x_524 = lean_ctor_get(x_519, 0);
lean_inc(x_524);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 x_525 = x_519;
} else {
 lean_dec_ref(x_519);
 x_525 = lean_box(0);
}
if (lean_is_scalar(x_525)) {
 x_526 = lean_alloc_ctor(0, 1, 0);
} else {
 x_526 = x_525;
}
lean_ctor_set(x_526, 0, x_524);
if (lean_is_scalar(x_523)) {
 x_527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_527 = x_523;
}
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_522);
if (lean_is_scalar(x_521)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_521;
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_520);
return x_528;
}
else
{
lean_object* x_529; lean_object* x_530; 
lean_dec(x_519);
x_529 = lean_ctor_get(x_517, 1);
lean_inc(x_529);
lean_dec(x_517);
x_530 = lean_ctor_get(x_518, 1);
lean_inc(x_530);
lean_dec(x_518);
x_2 = x_502;
x_3 = x_530;
x_10 = x_529;
goto _start;
}
}
}
case 10:
{
lean_object* x_532; 
x_532 = lean_ctor_get(x_2, 1);
lean_inc(x_532);
lean_dec(x_2);
x_2 = x_532;
x_3 = x_446;
goto _start;
}
case 11:
{
lean_object* x_534; 
x_534 = lean_ctor_get(x_2, 2);
lean_inc(x_534);
lean_dec(x_2);
x_2 = x_534;
x_3 = x_446;
goto _start;
}
default: 
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_2);
x_536 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_446);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_10);
return x_538;
}
}
}
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_539 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1;
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_3);
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_10);
return x_541;
}
}
}
}
static lean_object* _init_l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasExprMVar(x_2);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__3;
x_15 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_17);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
lean_dec(x_27);
x_28 = 1;
x_29 = lean_box(x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = 1;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = l_Lean_Elab_Term_getMVarDecl(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_st_ref_get(x_9, x_17);
if (x_3 == 0)
{
uint8_t x_290; 
x_290 = 1;
x_20 = x_290;
goto block_289;
}
else
{
uint8_t x_291; 
x_291 = 0;
x_20 = x_291;
goto block_289;
}
block_289:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 6);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_18);
lean_inc(x_2);
x_25 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(x_2, x_18, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_8, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_8, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_8, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_8, 7);
lean_inc(x_36);
x_37 = lean_ctor_get(x_8, 8);
lean_inc(x_37);
x_38 = lean_ctor_get(x_8, 9);
lean_inc(x_38);
x_39 = lean_ctor_get(x_8, 10);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_41 = lean_ctor_get(x_8, 11);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
x_43 = l_Lean_replaceRef(x_2, x_34);
lean_dec(x_34);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_30);
lean_ctor_set(x_44, 2, x_31);
lean_ctor_set(x_44, 3, x_32);
lean_ctor_set(x_44, 4, x_33);
lean_ctor_set(x_44, 5, x_43);
lean_ctor_set(x_44, 6, x_35);
lean_ctor_set(x_44, 7, x_36);
lean_ctor_set(x_44, 8, x_37);
lean_ctor_set(x_44, 9, x_38);
lean_ctor_set(x_44, 10, x_39);
lean_ctor_set(x_44, 11, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*12, x_40);
lean_ctor_set_uint8(x_44, sizeof(void*)*12 + 1, x_42);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_45 = l_Lean_Elab_Term_ensureHasType(x_18, x_26, x_28, x_28, x_4, x_5, x_6, x_7, x_44, x_9, x_27);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_46);
x_48 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_1, x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
lean_dec(x_52);
x_53 = 0;
x_54 = lean_box(x_53);
lean_ctor_set(x_48, 0, x_54);
return x_48;
}
else
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = 0;
x_57 = lean_box(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_dec(x_48);
x_60 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_1, x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = 1;
x_64 = lean_box(x_63);
lean_ctor_set(x_60, 0, x_64);
return x_60;
}
else
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
x_66 = 1;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_45);
if (x_69 == 0)
{
return x_45;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_45, 0);
x_71 = lean_ctor_get(x_45, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_45);
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
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_25);
if (x_73 == 0)
{
return x_25;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_25, 0);
x_75 = lean_ctor_get(x_25, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_25);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_171; lean_object* x_172; lean_object* x_253; 
x_77 = lean_ctor_get(x_19, 1);
lean_inc(x_77);
lean_dec(x_19);
x_78 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Term_withDeclName___spec__3___rarg(x_9, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_18);
lean_inc(x_2);
x_253 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(x_2, x_18, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_box(0);
x_257 = lean_ctor_get(x_8, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_8, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_8, 2);
lean_inc(x_259);
x_260 = lean_ctor_get(x_8, 3);
lean_inc(x_260);
x_261 = lean_ctor_get(x_8, 4);
lean_inc(x_261);
x_262 = lean_ctor_get(x_8, 5);
lean_inc(x_262);
x_263 = lean_ctor_get(x_8, 6);
lean_inc(x_263);
x_264 = lean_ctor_get(x_8, 7);
lean_inc(x_264);
x_265 = lean_ctor_get(x_8, 8);
lean_inc(x_265);
x_266 = lean_ctor_get(x_8, 9);
lean_inc(x_266);
x_267 = lean_ctor_get(x_8, 10);
lean_inc(x_267);
x_268 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_269 = lean_ctor_get(x_8, 11);
lean_inc(x_269);
x_270 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
x_271 = l_Lean_replaceRef(x_2, x_262);
lean_dec(x_262);
lean_dec(x_2);
x_272 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_272, 0, x_257);
lean_ctor_set(x_272, 1, x_258);
lean_ctor_set(x_272, 2, x_259);
lean_ctor_set(x_272, 3, x_260);
lean_ctor_set(x_272, 4, x_261);
lean_ctor_set(x_272, 5, x_271);
lean_ctor_set(x_272, 6, x_263);
lean_ctor_set(x_272, 7, x_264);
lean_ctor_set(x_272, 8, x_265);
lean_ctor_set(x_272, 9, x_266);
lean_ctor_set(x_272, 10, x_267);
lean_ctor_set(x_272, 11, x_269);
lean_ctor_set_uint8(x_272, sizeof(void*)*12, x_268);
lean_ctor_set_uint8(x_272, sizeof(void*)*12 + 1, x_270);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_273 = l_Lean_Elab_Term_ensureHasType(x_18, x_254, x_256, x_256, x_4, x_5, x_6, x_7, x_272, x_9, x_255);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
lean_inc(x_274);
x_276 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_1, x_274, x_4, x_5, x_6, x_7, x_8, x_9, x_275);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_unbox(x_277);
lean_dec(x_277);
if (x_278 == 0)
{
lean_object* x_279; uint8_t x_280; 
lean_dec(x_274);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_dec(x_276);
x_280 = 0;
x_81 = x_280;
x_82 = x_279;
goto block_170;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_281 = lean_ctor_get(x_276, 1);
lean_inc(x_281);
lean_dec(x_276);
lean_inc(x_1);
x_282 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_1, x_274, x_4, x_5, x_6, x_7, x_8, x_9, x_281);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = 1;
x_81 = x_284;
x_82 = x_283;
goto block_170;
}
}
else
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_285 = lean_ctor_get(x_273, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_273, 1);
lean_inc(x_286);
lean_dec(x_273);
x_171 = x_285;
x_172 = x_286;
goto block_252;
}
}
else
{
lean_object* x_287; lean_object* x_288; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_287 = lean_ctor_get(x_253, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_253, 1);
lean_inc(x_288);
lean_dec(x_253);
x_171 = x_287;
x_172 = x_288;
goto block_252;
}
block_170:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_st_ref_take(x_9, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = !lean_is_exclusive(x_84);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_84, 6);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_85, 0);
x_91 = lean_ctor_get(x_85, 1);
x_92 = lean_ctor_get(x_91, 2);
lean_inc(x_92);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_nat_dec_lt(x_93, x_92);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_1);
lean_ctor_set(x_85, 1, x_79);
x_95 = lean_st_ref_set(x_9, x_84, x_86);
lean_dec(x_9);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
x_98 = lean_box(x_81);
lean_ctor_set(x_95, 0, x_98);
return x_95;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_box(x_81);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_sub(x_92, x_102);
lean_dec(x_92);
x_104 = l_Lean_Elab_instInhabitedInfoTree;
x_105 = l_Lean_PersistentArray_get_x21___rarg(x_104, x_91, x_103);
lean_dec(x_103);
x_106 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_90, x_1, x_105);
lean_ctor_set(x_85, 1, x_79);
lean_ctor_set(x_85, 0, x_106);
x_107 = lean_st_ref_set(x_9, x_84, x_86);
lean_dec(x_9);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_107, 0);
lean_dec(x_109);
x_110 = lean_box(x_81);
lean_ctor_set(x_107, 0, x_110);
return x_107;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_112 = lean_box(x_81);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
else
{
uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_114 = lean_ctor_get_uint8(x_85, sizeof(void*)*2);
x_115 = lean_ctor_get(x_85, 0);
x_116 = lean_ctor_get(x_85, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_85);
x_117 = lean_ctor_get(x_116, 2);
lean_inc(x_117);
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_nat_dec_lt(x_118, x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_1);
x_120 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_79);
lean_ctor_set_uint8(x_120, sizeof(void*)*2, x_114);
lean_ctor_set(x_84, 6, x_120);
x_121 = lean_st_ref_set(x_9, x_84, x_86);
lean_dec(x_9);
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
x_124 = lean_box(x_81);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_sub(x_117, x_126);
lean_dec(x_117);
x_128 = l_Lean_Elab_instInhabitedInfoTree;
x_129 = l_Lean_PersistentArray_get_x21___rarg(x_128, x_116, x_127);
lean_dec(x_127);
x_130 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_115, x_1, x_129);
x_131 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_79);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_114);
lean_ctor_set(x_84, 6, x_131);
x_132 = lean_st_ref_set(x_9, x_84, x_86);
lean_dec(x_9);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = lean_box(x_81);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_137 = lean_ctor_get(x_84, 0);
x_138 = lean_ctor_get(x_84, 1);
x_139 = lean_ctor_get(x_84, 2);
x_140 = lean_ctor_get(x_84, 3);
x_141 = lean_ctor_get(x_84, 4);
x_142 = lean_ctor_get(x_84, 5);
x_143 = lean_ctor_get(x_84, 7);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_84);
x_144 = lean_ctor_get_uint8(x_85, sizeof(void*)*2);
x_145 = lean_ctor_get(x_85, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_85, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_147 = x_85;
} else {
 lean_dec_ref(x_85);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_146, 2);
lean_inc(x_148);
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_nat_dec_lt(x_149, x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_1);
if (lean_is_scalar(x_147)) {
 x_151 = lean_alloc_ctor(0, 2, 1);
} else {
 x_151 = x_147;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_79);
lean_ctor_set_uint8(x_151, sizeof(void*)*2, x_144);
x_152 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_152, 0, x_137);
lean_ctor_set(x_152, 1, x_138);
lean_ctor_set(x_152, 2, x_139);
lean_ctor_set(x_152, 3, x_140);
lean_ctor_set(x_152, 4, x_141);
lean_ctor_set(x_152, 5, x_142);
lean_ctor_set(x_152, 6, x_151);
lean_ctor_set(x_152, 7, x_143);
x_153 = lean_st_ref_set(x_9, x_152, x_86);
lean_dec(x_9);
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
x_156 = lean_box(x_81);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_nat_sub(x_148, x_158);
lean_dec(x_148);
x_160 = l_Lean_Elab_instInhabitedInfoTree;
x_161 = l_Lean_PersistentArray_get_x21___rarg(x_160, x_146, x_159);
lean_dec(x_159);
x_162 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_145, x_1, x_161);
if (lean_is_scalar(x_147)) {
 x_163 = lean_alloc_ctor(0, 2, 1);
} else {
 x_163 = x_147;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_79);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_144);
x_164 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_164, 0, x_137);
lean_ctor_set(x_164, 1, x_138);
lean_ctor_set(x_164, 2, x_139);
lean_ctor_set(x_164, 3, x_140);
lean_ctor_set(x_164, 4, x_141);
lean_ctor_set(x_164, 5, x_142);
lean_ctor_set(x_164, 6, x_163);
lean_ctor_set(x_164, 7, x_143);
x_165 = lean_st_ref_set(x_9, x_164, x_86);
lean_dec(x_9);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
x_168 = lean_box(x_81);
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_167;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_166);
return x_169;
}
}
}
block_252:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_173 = lean_st_ref_take(x_9, x_172);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_174, 6);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_177 = !lean_is_exclusive(x_174);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_174, 6);
lean_dec(x_178);
x_179 = !lean_is_exclusive(x_175);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_180 = lean_ctor_get(x_175, 0);
x_181 = lean_ctor_get(x_175, 1);
x_182 = lean_ctor_get(x_181, 2);
lean_inc(x_182);
x_183 = lean_unsigned_to_nat(0u);
x_184 = lean_nat_dec_lt(x_183, x_182);
if (x_184 == 0)
{
lean_object* x_185; uint8_t x_186; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_1);
lean_ctor_set(x_175, 1, x_79);
x_185 = lean_st_ref_set(x_9, x_174, x_176);
lean_dec(x_9);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; 
x_187 = lean_ctor_get(x_185, 0);
lean_dec(x_187);
lean_ctor_set_tag(x_185, 1);
lean_ctor_set(x_185, 0, x_171);
return x_185;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_171);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_nat_sub(x_182, x_190);
lean_dec(x_182);
x_192 = l_Lean_Elab_instInhabitedInfoTree;
x_193 = l_Lean_PersistentArray_get_x21___rarg(x_192, x_181, x_191);
lean_dec(x_191);
x_194 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_180, x_1, x_193);
lean_ctor_set(x_175, 1, x_79);
lean_ctor_set(x_175, 0, x_194);
x_195 = lean_st_ref_set(x_9, x_174, x_176);
lean_dec(x_9);
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_195, 0);
lean_dec(x_197);
lean_ctor_set_tag(x_195, 1);
lean_ctor_set(x_195, 0, x_171);
return x_195;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_171);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get_uint8(x_175, sizeof(void*)*2);
x_201 = lean_ctor_get(x_175, 0);
x_202 = lean_ctor_get(x_175, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_175);
x_203 = lean_ctor_get(x_202, 2);
lean_inc(x_203);
x_204 = lean_unsigned_to_nat(0u);
x_205 = lean_nat_dec_lt(x_204, x_203);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_1);
x_206 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_206, 0, x_201);
lean_ctor_set(x_206, 1, x_79);
lean_ctor_set_uint8(x_206, sizeof(void*)*2, x_200);
lean_ctor_set(x_174, 6, x_206);
x_207 = lean_st_ref_set(x_9, x_174, x_176);
lean_dec(x_9);
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
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
 lean_ctor_set_tag(x_210, 1);
}
lean_ctor_set(x_210, 0, x_171);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_nat_sub(x_203, x_211);
lean_dec(x_203);
x_213 = l_Lean_Elab_instInhabitedInfoTree;
x_214 = l_Lean_PersistentArray_get_x21___rarg(x_213, x_202, x_212);
lean_dec(x_212);
x_215 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_201, x_1, x_214);
x_216 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_79);
lean_ctor_set_uint8(x_216, sizeof(void*)*2, x_200);
lean_ctor_set(x_174, 6, x_216);
x_217 = lean_st_ref_set(x_9, x_174, x_176);
lean_dec(x_9);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
 lean_ctor_set_tag(x_220, 1);
}
lean_ctor_set(x_220, 0, x_171);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_221 = lean_ctor_get(x_174, 0);
x_222 = lean_ctor_get(x_174, 1);
x_223 = lean_ctor_get(x_174, 2);
x_224 = lean_ctor_get(x_174, 3);
x_225 = lean_ctor_get(x_174, 4);
x_226 = lean_ctor_get(x_174, 5);
x_227 = lean_ctor_get(x_174, 7);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_174);
x_228 = lean_ctor_get_uint8(x_175, sizeof(void*)*2);
x_229 = lean_ctor_get(x_175, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_175, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_231 = x_175;
} else {
 lean_dec_ref(x_175);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_230, 2);
lean_inc(x_232);
x_233 = lean_unsigned_to_nat(0u);
x_234 = lean_nat_dec_lt(x_233, x_232);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_232);
lean_dec(x_230);
lean_dec(x_1);
if (lean_is_scalar(x_231)) {
 x_235 = lean_alloc_ctor(0, 2, 1);
} else {
 x_235 = x_231;
}
lean_ctor_set(x_235, 0, x_229);
lean_ctor_set(x_235, 1, x_79);
lean_ctor_set_uint8(x_235, sizeof(void*)*2, x_228);
x_236 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_236, 0, x_221);
lean_ctor_set(x_236, 1, x_222);
lean_ctor_set(x_236, 2, x_223);
lean_ctor_set(x_236, 3, x_224);
lean_ctor_set(x_236, 4, x_225);
lean_ctor_set(x_236, 5, x_226);
lean_ctor_set(x_236, 6, x_235);
lean_ctor_set(x_236, 7, x_227);
x_237 = lean_st_ref_set(x_9, x_236, x_176);
lean_dec(x_9);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_239 = x_237;
} else {
 lean_dec_ref(x_237);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
 lean_ctor_set_tag(x_240, 1);
}
lean_ctor_set(x_240, 0, x_171);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_nat_sub(x_232, x_241);
lean_dec(x_232);
x_243 = l_Lean_Elab_instInhabitedInfoTree;
x_244 = l_Lean_PersistentArray_get_x21___rarg(x_243, x_230, x_242);
lean_dec(x_242);
x_245 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_229, x_1, x_244);
if (lean_is_scalar(x_231)) {
 x_246 = lean_alloc_ctor(0, 2, 1);
} else {
 x_246 = x_231;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_79);
lean_ctor_set_uint8(x_246, sizeof(void*)*2, x_228);
x_247 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_247, 0, x_221);
lean_ctor_set(x_247, 1, x_222);
lean_ctor_set(x_247, 2, x_223);
lean_ctor_set(x_247, 3, x_224);
lean_ctor_set(x_247, 4, x_225);
lean_ctor_set(x_247, 5, x_226);
lean_ctor_set(x_247, 6, x_246);
lean_ctor_set(x_247, 7, x_227);
x_248 = lean_st_ref_set(x_9, x_247, x_176);
lean_dec(x_9);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
 lean_ctor_set_tag(x_251, 1);
}
lean_ctor_set(x_251, 0, x_171);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = lean_box(0);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = lean_box(0);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_postponeExceptionId;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Elab_Term_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_box(x_3);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1___boxed), 10, 3);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_27);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_Elab_Term_withSavedContext___rarg(x_4, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(0);
lean_ctor_set(x_23, 1, x_32);
lean_ctor_set(x_23, 0, x_30);
x_12 = x_23;
x_13 = x_31;
goto block_22;
}
else
{
uint8_t x_33; 
lean_free_object(x_23);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
x_36 = l_Lean_Exception_isInterrupt(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Exception_isRuntime(x_34);
if (x_37 == 0)
{
if (lean_obj_tag(x_34) == 0)
{
lean_free_object(x_29);
if (x_3 == 0)
{
lean_object* x_38; 
lean_dec(x_25);
x_38 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_12 = x_40;
x_13 = x_39;
goto block_22;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_34);
x_45 = 1;
x_46 = l_Lean_Elab_Term_SavedState_restore(x_25, x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_48;
x_13 = x_47;
goto block_22;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_34, 0);
lean_inc(x_49);
x_50 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3;
x_51 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_dec(x_25);
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
uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_29);
lean_dec(x_34);
x_52 = 1;
x_53 = l_Lean_Elab_Term_SavedState_restore(x_25, x_52, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_55;
x_13 = x_54;
goto block_22;
}
}
}
else
{
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_29;
}
}
else
{
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_29;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_29, 0);
x_57 = lean_ctor_get(x_29, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_29);
x_58 = l_Lean_Exception_isInterrupt(x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Exception_isRuntime(x_56);
if (x_59 == 0)
{
if (lean_obj_tag(x_56) == 0)
{
if (x_3 == 0)
{
lean_object* x_60; 
lean_dec(x_25);
x_60 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_12 = x_62;
x_13 = x_61;
goto block_22;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_65 = x_60;
} else {
 lean_dec_ref(x_60);
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
else
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_56);
x_67 = 1;
x_68 = l_Lean_Elab_Term_SavedState_restore(x_25, x_67, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_70;
x_13 = x_69;
goto block_22;
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_56, 0);
lean_inc(x_71);
x_72 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3;
x_73 = lean_nat_dec_eq(x_71, x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_56);
lean_ctor_set(x_74, 1, x_57);
return x_74;
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_56);
x_75 = 1;
x_76 = l_Lean_Elab_Term_SavedState_restore(x_25, x_75, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_78;
x_13 = x_77;
goto block_22;
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_56);
lean_ctor_set(x_79, 1, x_57);
return x_79;
}
}
else
{
lean_object* x_80; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_56);
lean_ctor_set(x_80, 1, x_57);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_23, 0);
x_82 = lean_ctor_get(x_23, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_23);
x_83 = lean_box(x_3);
x_84 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1___boxed), 10, 3);
lean_closure_set(x_84, 0, x_1);
lean_closure_set(x_84, 1, x_2);
lean_closure_set(x_84, 2, x_83);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_85 = l_Lean_Elab_Term_withSavedContext___rarg(x_4, x_84, x_5, x_6, x_7, x_8, x_9, x_10, x_82);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_81);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_12 = x_89;
x_13 = x_87;
goto block_22;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
 x_92 = lean_box(0);
}
x_93 = l_Lean_Exception_isInterrupt(x_90);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Exception_isRuntime(x_90);
if (x_94 == 0)
{
if (lean_obj_tag(x_90) == 0)
{
lean_dec(x_92);
if (x_3 == 0)
{
lean_object* x_95; 
lean_dec(x_81);
x_95 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_90, x_5, x_6, x_7, x_8, x_9, x_10, x_91);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1;
x_12 = x_97;
x_13 = x_96;
goto block_22;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
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
else
{
uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
x_102 = 1;
x_103 = l_Lean_Elab_Term_SavedState_restore(x_81, x_102, x_5, x_6, x_7, x_8, x_9, x_10, x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_105;
x_13 = x_104;
goto block_22;
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_90, 0);
lean_inc(x_106);
x_107 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3;
x_108 = lean_nat_dec_eq(x_106, x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_81);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_92)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_92;
}
lean_ctor_set(x_109, 0, x_90);
lean_ctor_set(x_109, 1, x_91);
return x_109;
}
else
{
uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_92);
lean_dec(x_90);
x_110 = 1;
x_111 = l_Lean_Elab_Term_SavedState_restore(x_81, x_110, x_5, x_6, x_7, x_8, x_9, x_10, x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2;
x_12 = x_113;
x_13 = x_112;
goto block_22;
}
}
}
else
{
lean_object* x_114; 
lean_dec(x_81);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_92)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_92;
}
lean_ctor_set(x_114, 0, x_90);
lean_ctor_set(x_114, 1, x_91);
return x_114;
}
}
else
{
lean_object* x_115; 
lean_dec(x_81);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_92)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_92;
}
lean_ctor_set(x_115, 0, x_90);
lean_ctor_set(x_115, 1, x_91);
return x_115;
}
}
}
block_22:
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_12, 1, x_13);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_12, 1);
lean_dec(x_19);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 1, x_13);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_box(x_4);
lean_inc(x_2);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___boxed), 11, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_1);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 5);
x_16 = l_Lean_replaceRef(x_2, x_15);
lean_dec(x_15);
lean_dec(x_2);
lean_ctor_set(x_9, 5, x_16);
x_17 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_9, 2);
x_21 = lean_ctor_get(x_9, 3);
x_22 = lean_ctor_get(x_9, 4);
x_23 = lean_ctor_get(x_9, 5);
x_24 = lean_ctor_get(x_9, 6);
x_25 = lean_ctor_get(x_9, 7);
x_26 = lean_ctor_get(x_9, 8);
x_27 = lean_ctor_get(x_9, 9);
x_28 = lean_ctor_get(x_9, 10);
x_29 = lean_ctor_get_uint8(x_9, sizeof(void*)*12);
x_30 = lean_ctor_get(x_9, 11);
x_31 = lean_ctor_get_uint8(x_9, sizeof(void*)*12 + 1);
lean_inc(x_30);
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
lean_inc(x_18);
lean_dec(x_9);
x_32 = l_Lean_replaceRef(x_2, x_23);
lean_dec(x_23);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_19);
lean_ctor_set(x_33, 2, x_20);
lean_ctor_set(x_33, 3, x_21);
lean_ctor_set(x_33, 4, x_22);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_24);
lean_ctor_set(x_33, 7, x_25);
lean_ctor_set(x_33, 8, x_26);
lean_ctor_set(x_33, 9, x_27);
lean_ctor_set(x_33, 10, x_28);
lean_ctor_set(x_33, 11, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*12, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*12 + 1, x_31);
x_34 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_3, x_13, x_5, x_6, x_7, x_8, x_33, x_10, x_11);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getDelayedMVarAssignment_x3f___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_occursCheck_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.SyntheticMVars", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.SyntheticMVars.0.Lean.Elab.Term.synthesizePendingInstMVar", 76, 76);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(69u);
x_4 = lean_unsigned_to_nat(26u);
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
x_19 = l_Lean_Exception_isInterrupt(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Exception_isRuntime(x_17);
if (x_20 == 0)
{
lean_free_object(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_17);
x_34 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4;
x_35 = l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1(x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
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
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = l_Lean_Exception_isInterrupt(x_44);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Exception_isRuntime(x_44);
if (x_47 == 0)
{
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_48; 
x_48 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = 1;
x_52 = lean_box(x_51);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_44);
x_58 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4;
x_59 = l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1(x_58, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_66 = x_59;
} else {
 lean_dec_ref(x_59);
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
else
{
lean_object* x_68; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_44);
lean_ctor_set(x_68, 1, x_45);
return x_68;
}
}
else
{
lean_object* x_69; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_44);
lean_ctor_set(x_69, 1, x_45);
return x_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___boxed), 10, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
x_12 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_26; 
x_9 = l_Lean_Elab_Term_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_12);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = 0;
x_31 = l_Lean_Elab_Term_SavedState_restore(x_10, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(x_30);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
lean_dec(x_39);
x_40 = 1;
x_41 = lean_box(x_40);
lean_ctor_set(x_26, 0, x_41);
return x_26;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_dec(x_26);
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_26, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_26, 1);
lean_inc(x_47);
lean_dec(x_26);
x_13 = x_46;
x_14 = x_47;
goto block_25;
}
block_25:
{
uint8_t x_15; 
x_15 = l_Lean_Exception_isInterrupt(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Exception_isRuntime(x_13);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_17 = 0;
x_18 = l_Lean_Elab_Term_SavedState_restore(x_10, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
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
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_12)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_12;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_12)) {
 x_24 = lean_alloc_ctor(1, 2, 0);
} else {
 x_24 = x_12;
 lean_ctor_set_tag(x_24, 1);
}
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_14);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_2, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
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
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = l_Lean_Exception_isInterrupt(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Exception_isRuntime(x_16);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = 0;
x_20 = lean_box(x_19);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
return x_10;
}
}
else
{
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = l_Lean_Exception_isInterrupt(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_21);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___lambda__1), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg), 9, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_commitWhen___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_12);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_13;
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
lean_object* x_19; 
lean_free_object(x_1);
lean_dec(x_12);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_1 = x_13;
x_9 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_25);
x_27 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_2);
x_1 = x_26;
x_2 = x_31;
x_9 = x_30;
goto _start;
}
else
{
lean_object* x_33; 
lean_dec(x_25);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_1 = x_26;
x_9 = x_33;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_37 = x_27;
} else {
 lean_dec_ref(x_27);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep___spec__1(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_List_reverse___rarg(x_12);
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
x_16 = l_List_reverse___rarg(x_14);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstancesStep(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_List_lengthTRAux___rarg(x_11, x_13);
x_15 = l_List_lengthTRAux___rarg(x_1, x_13);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
if (x_16 == 0)
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
lean_free_object(x_9);
x_1 = x_11;
x_8 = x_12;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_List_lengthTRAux___rarg(x_18, x_20);
x_22 = l_List_lengthTRAux___rarg(x_1, x_20);
lean_dec(x_1);
x_23 = lean_nat_dec_lt(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
else
{
x_1 = x_18;
x_8 = x_19;
goto _start;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_defaultInstanceExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_defaultInstanceExtension;
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_10 = l_Lean_Meta_instInhabitedDefaultInstances;
x_11 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1;
x_12 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_10, x_11, x_6, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_defaultInstanceExtension;
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
lean_dec(x_18);
x_20 = l_Lean_Meta_instInhabitedDefaultInstances;
x_21 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1;
x_22 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_20, x_21, x_16, x_19);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___boxed), 2, 0);
return x_6;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 3);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_24 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(x_1, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_10 = x_27;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_11 = _tmp_10;
}
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_24, 0);
lean_dec(x_30);
x_31 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__3;
lean_ctor_set(x_24, 0, x_31);
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__3;
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
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
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
uint8_t x_39; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1() {
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
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2(x_1, x_12, x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__2;
x_19 = lean_box(0);
x_20 = lean_apply_8(x_18, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
return x_20;
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
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_defaultInstanceExtension;
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
lean_dec(x_14);
x_16 = l_Lean_Meta_instInhabitedDefaultInstances;
x_17 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1;
x_18 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_16, x_17, x_12, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_19, x_1);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_defaultInstanceExtension;
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*3);
lean_dec(x_27);
x_29 = l_Lean_Meta_instInhabitedDefaultInstances;
x_30 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1;
x_31 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_29, x_30, x_25, x_28);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_32, x_1);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_8);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_nat_dec_eq(x_21, x_2);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_20);
lean_inc(x_5);
{
lean_object* _tmp_6 = x_19;
lean_object* _tmp_7 = x_5;
lean_object* _tmp_8 = lean_box(0);
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_24; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_24 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance(x_1, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_5);
{
lean_object* _tmp_6 = x_19;
lean_object* _tmp_7 = x_5;
lean_object* _tmp_8 = lean_box(0);
lean_object* _tmp_15 = x_27;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_16 = _tmp_15;
}
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_24, 0);
lean_dec(x_30);
x_31 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2;
lean_ctor_set(x_24, 0, x_31);
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2;
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
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_isClass_x3f(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = l_Lean_Meta_getDefaultInstances___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__1(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = 0;
x_30 = lean_box(x_29);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_box(0);
x_37 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_38 = l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2(x_1, x_2, x_26, x_36, x_37, x_26, x_26, x_37, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_26);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__2;
x_43 = lean_box(0);
x_44 = lean_apply_8(x_42, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
return x_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_38, 0);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_38);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
return x_13;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_13, 0);
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_10);
if (x_59 == 0)
{
return x_10;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_10, 0);
x_61 = lean_ctor_get(x_10, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_10);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lambda__1___boxed), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_nat_dec_lt(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_array_fget(x_2, x_5);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
x_20 = 3;
x_21 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_5 = x_23;
x_6 = lean_box(0);
x_7 = lean_box(0);
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = l_Lean_instInhabitedExpr;
x_26 = lean_array_get(x_25, x_1, x_5);
x_27 = l_Lean_Expr_mvarId_x21(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
x_29 = lean_ctor_get(x_3, 2);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_4 = x_28;
x_5 = x_30;
x_6 = lean_box(0);
x_7 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_box(0);
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1(x_2, x_1, x_15, x_11, x_13, lean_box(0), lean_box(0), x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isDefEq worked ", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" =\?= ", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = l_Lean_Expr_mvar___override(x_1);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 6);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; uint8_t x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_25 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
x_26 = 1;
lean_ctor_set_uint8(x_15, 7, x_26);
x_27 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_15);
x_28 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 2, x_18);
lean_ctor_set(x_28, 3, x_19);
lean_ctor_set(x_28, 4, x_20);
lean_ctor_set(x_28, 5, x_21);
lean_ctor_set(x_28, 6, x_22);
lean_ctor_set_uint64(x_28, sizeof(void*)*7, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*7 + 8, x_16);
lean_ctor_set_uint8(x_28, sizeof(void*)*7 + 9, x_24);
lean_ctor_set_uint8(x_28, sizeof(void*)*7 + 10, x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_14);
x_29 = l_Lean_Meta_isExprDefEqGuarded(x_14, x_2, x_28, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set(x_29, 0, x_35);
return x_29;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_dec(x_29);
lean_inc(x_3);
x_41 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(x_4, x_5, x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
return x_46;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_41, 1);
x_49 = lean_ctor_get(x_41, 0);
lean_dec(x_49);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_14);
x_50 = lean_infer_type(x_14, x_9, x_10, x_11, x_12, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_53 = lean_infer_type(x_2, x_9, x_10, x_11, x_12, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_MessageData_ofExpr(x_14);
x_57 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2;
lean_ctor_set_tag(x_41, 7);
lean_ctor_set(x_41, 1, x_56);
lean_ctor_set(x_41, 0, x_57);
x_58 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_41);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_MessageData_ofExpr(x_51);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_MessageData_ofExpr(x_2);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_58);
x_67 = l_Lean_MessageData_ofExpr(x_54);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_3, x_70, x_7, x_8, x_9, x_10, x_11, x_12, x_55);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(x_4, x_5, x_72, x_7, x_8, x_9, x_10, x_11, x_12, x_73);
lean_dec(x_72);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_51);
lean_free_object(x_41);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_53);
if (x_75 == 0)
{
return x_53;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_53, 0);
x_77 = lean_ctor_get(x_53, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_free_object(x_41);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_50);
if (x_79 == 0)
{
return x_50;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_50, 0);
x_81 = lean_ctor_get(x_50, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_50);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_41, 1);
lean_inc(x_83);
lean_dec(x_41);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_14);
x_84 = lean_infer_type(x_14, x_9, x_10, x_11, x_12, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_87 = lean_infer_type(x_2, x_9, x_10, x_11, x_12, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_MessageData_ofExpr(x_14);
x_91 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_MessageData_ofExpr(x_85);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_MessageData_ofExpr(x_2);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_93);
x_102 = l_Lean_MessageData_ofExpr(x_88);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_3, x_105, x_7, x_8, x_9, x_10, x_11, x_12, x_89);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(x_4, x_5, x_107, x_7, x_8, x_9, x_10, x_11, x_12, x_108);
lean_dec(x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_85);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_87, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_87, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_112 = x_87;
} else {
 lean_dec_ref(x_87);
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
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_ctor_get(x_84, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_84, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_116 = x_84;
} else {
 lean_dec_ref(x_84);
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
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_29);
if (x_118 == 0)
{
return x_29;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_29, 0);
x_120 = lean_ctor_get(x_29, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_29);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; lean_object* x_142; uint64_t x_143; lean_object* x_144; lean_object* x_145; 
x_122 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_123 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
x_124 = lean_ctor_get_uint8(x_15, 0);
x_125 = lean_ctor_get_uint8(x_15, 1);
x_126 = lean_ctor_get_uint8(x_15, 2);
x_127 = lean_ctor_get_uint8(x_15, 3);
x_128 = lean_ctor_get_uint8(x_15, 4);
x_129 = lean_ctor_get_uint8(x_15, 5);
x_130 = lean_ctor_get_uint8(x_15, 6);
x_131 = lean_ctor_get_uint8(x_15, 8);
x_132 = lean_ctor_get_uint8(x_15, 9);
x_133 = lean_ctor_get_uint8(x_15, 10);
x_134 = lean_ctor_get_uint8(x_15, 11);
x_135 = lean_ctor_get_uint8(x_15, 12);
x_136 = lean_ctor_get_uint8(x_15, 13);
x_137 = lean_ctor_get_uint8(x_15, 14);
x_138 = lean_ctor_get_uint8(x_15, 15);
x_139 = lean_ctor_get_uint8(x_15, 16);
x_140 = lean_ctor_get_uint8(x_15, 17);
lean_dec(x_15);
x_141 = 1;
x_142 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_142, 0, x_124);
lean_ctor_set_uint8(x_142, 1, x_125);
lean_ctor_set_uint8(x_142, 2, x_126);
lean_ctor_set_uint8(x_142, 3, x_127);
lean_ctor_set_uint8(x_142, 4, x_128);
lean_ctor_set_uint8(x_142, 5, x_129);
lean_ctor_set_uint8(x_142, 6, x_130);
lean_ctor_set_uint8(x_142, 7, x_141);
lean_ctor_set_uint8(x_142, 8, x_131);
lean_ctor_set_uint8(x_142, 9, x_132);
lean_ctor_set_uint8(x_142, 10, x_133);
lean_ctor_set_uint8(x_142, 11, x_134);
lean_ctor_set_uint8(x_142, 12, x_135);
lean_ctor_set_uint8(x_142, 13, x_136);
lean_ctor_set_uint8(x_142, 14, x_137);
lean_ctor_set_uint8(x_142, 15, x_138);
lean_ctor_set_uint8(x_142, 16, x_139);
lean_ctor_set_uint8(x_142, 17, x_140);
x_143 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_142);
x_144 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_17);
lean_ctor_set(x_144, 2, x_18);
lean_ctor_set(x_144, 3, x_19);
lean_ctor_set(x_144, 4, x_20);
lean_ctor_set(x_144, 5, x_21);
lean_ctor_set(x_144, 6, x_22);
lean_ctor_set_uint64(x_144, sizeof(void*)*7, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*7 + 8, x_16);
lean_ctor_set_uint8(x_144, sizeof(void*)*7 + 9, x_122);
lean_ctor_set_uint8(x_144, sizeof(void*)*7 + 10, x_123);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_14);
x_145 = l_Lean_Meta_isExprDefEqGuarded(x_14, x_2, x_144, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_149 = x_145;
} else {
 lean_dec_ref(x_145);
 x_149 = lean_box(0);
}
x_150 = 0;
x_151 = lean_box(x_150);
if (lean_is_scalar(x_149)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_149;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_148);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_153 = lean_ctor_get(x_145, 1);
lean_inc(x_153);
lean_dec(x_145);
lean_inc(x_3);
x_154 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_unbox(x_155);
lean_dec(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_box(0);
x_159 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(x_4, x_5, x_158, x_7, x_8, x_9, x_10, x_11, x_12, x_157);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_161 = x_154;
} else {
 lean_dec_ref(x_154);
 x_161 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_14);
x_162 = lean_infer_type(x_14, x_9, x_10, x_11, x_12, x_160);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_165 = lean_infer_type(x_2, x_9, x_10, x_11, x_12, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l_Lean_MessageData_ofExpr(x_14);
x_169 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2;
if (lean_is_scalar(x_161)) {
 x_170 = lean_alloc_ctor(7, 2, 0);
} else {
 x_170 = x_161;
 lean_ctor_set_tag(x_170, 7);
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_MessageData_ofExpr(x_163);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_MessageData_ofExpr(x_2);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_171);
x_180 = l_Lean_MessageData_ofExpr(x_166);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_3, x_183, x_7, x_8, x_9, x_10, x_11, x_12, x_167);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(x_4, x_5, x_185, x_7, x_8, x_9, x_10, x_11, x_12, x_186);
lean_dec(x_185);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_188 = lean_ctor_get(x_165, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_165, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_190 = x_165;
} else {
 lean_dec_ref(x_165);
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
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_161);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_192 = lean_ctor_get(x_162, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_162, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_194 = x_162;
} else {
 lean_dec_ref(x_162);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_196 = lean_ctor_get(x_145, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_145, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_198 = x_145;
} else {
 lean_dec_ref(x_145);
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
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defaultInstance", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_13 = lean_infer_type(x_11, x_5, x_6, x_7, x_8, x_12);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_14, x_17, x_16, x_18, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_dec(x_28);
x_29 = l_Lean_mkAppN(x_11, x_24);
x_30 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__3;
x_31 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_21);
lean_free_object(x_20);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(x_2, x_29, x_30, x_27, x_24, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_24);
lean_dec(x_27);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_31, 1);
x_39 = lean_ctor_get(x_31, 0);
lean_dec(x_39);
lean_inc(x_2);
x_40 = l_Lean_Expr_mvar___override(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_40);
x_41 = lean_infer_type(x_40, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_44 = lean_infer_type(x_29, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_expr_dbg_to_string(x_40);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
x_49 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_48);
lean_ctor_set(x_31, 0, x_49);
x_50 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5;
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_50);
lean_ctor_set(x_21, 0, x_31);
x_51 = l_Lean_MessageData_ofExpr(x_40);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_51);
lean_ctor_set(x_20, 0, x_21);
x_52 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_20);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_MessageData_ofExpr(x_42);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_inc(x_29);
x_58 = l_Lean_MessageData_ofExpr(x_29);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_52);
x_61 = l_Lean_MessageData_ofExpr(x_45);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_49);
x_64 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_30, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(x_2, x_29, x_30, x_27, x_24, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
lean_dec(x_65);
lean_dec(x_24);
lean_dec(x_27);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_42);
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_29);
lean_free_object(x_21);
lean_dec(x_27);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_44);
if (x_68 == 0)
{
return x_44;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_44, 0);
x_70 = lean_ctor_get(x_44, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_44);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_40);
lean_free_object(x_31);
lean_dec(x_29);
lean_free_object(x_21);
lean_dec(x_27);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_41);
if (x_72 == 0)
{
return x_41;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_41, 0);
x_74 = lean_ctor_get(x_41, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_41);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_31, 1);
lean_inc(x_76);
lean_dec(x_31);
lean_inc(x_2);
x_77 = l_Lean_Expr_mvar___override(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_77);
x_78 = lean_infer_type(x_77, x_5, x_6, x_7, x_8, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_81 = lean_infer_type(x_29, x_5, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_expr_dbg_to_string(x_77);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
x_86 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5;
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_88);
lean_ctor_set(x_21, 0, x_87);
x_89 = l_Lean_MessageData_ofExpr(x_77);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_89);
lean_ctor_set(x_20, 0, x_21);
x_90 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_20);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_MessageData_ofExpr(x_79);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_29);
x_96 = l_Lean_MessageData_ofExpr(x_29);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_90);
x_99 = l_Lean_MessageData_ofExpr(x_82);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_86);
x_102 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_30, x_101, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(x_2, x_29, x_30, x_27, x_24, x_103, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
lean_dec(x_103);
lean_dec(x_24);
lean_dec(x_27);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_29);
lean_free_object(x_21);
lean_dec(x_27);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_ctor_get(x_81, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_81, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_108 = x_81;
} else {
 lean_dec_ref(x_81);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_77);
lean_dec(x_29);
lean_free_object(x_21);
lean_dec(x_27);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_78, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_78, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_112 = x_78;
} else {
 lean_dec_ref(x_78);
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
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_114 = lean_ctor_get(x_21, 0);
lean_inc(x_114);
lean_dec(x_21);
x_115 = l_Lean_mkAppN(x_11, x_24);
x_116 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__3;
x_117 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_116, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_free_object(x_20);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_box(0);
x_122 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(x_2, x_115, x_116, x_114, x_24, x_121, x_3, x_4, x_5, x_6, x_7, x_8, x_120);
lean_dec(x_24);
lean_dec(x_114);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
 x_124 = lean_box(0);
}
lean_inc(x_2);
x_125 = l_Lean_Expr_mvar___override(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_125);
x_126 = lean_infer_type(x_125, x_5, x_6, x_7, x_8, x_123);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_115);
x_129 = lean_infer_type(x_115, x_5, x_6, x_7, x_8, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_expr_dbg_to_string(x_125);
x_133 = l_Lean_stringToMessageData(x_132);
lean_dec(x_132);
x_134 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
if (lean_is_scalar(x_124)) {
 x_135 = lean_alloc_ctor(7, 2, 0);
} else {
 x_135 = x_124;
 lean_ctor_set_tag(x_135, 7);
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_MessageData_ofExpr(x_125);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_138);
lean_ctor_set(x_20, 0, x_137);
x_139 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_20);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_MessageData_ofExpr(x_127);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_115);
x_145 = l_Lean_MessageData_ofExpr(x_115);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_139);
x_148 = l_Lean_MessageData_ofExpr(x_130);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_134);
x_151 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_116, x_150, x_3, x_4, x_5, x_6, x_7, x_8, x_131);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(x_2, x_115, x_116, x_114, x_24, x_152, x_3, x_4, x_5, x_6, x_7, x_8, x_153);
lean_dec(x_152);
lean_dec(x_24);
lean_dec(x_114);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_115);
lean_dec(x_114);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_ctor_get(x_129, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_129, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_157 = x_129;
} else {
 lean_dec_ref(x_129);
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
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_115);
lean_dec(x_114);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_159 = lean_ctor_get(x_126, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_126, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_161 = x_126;
} else {
 lean_dec_ref(x_126);
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
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_163 = lean_ctor_get(x_20, 0);
lean_inc(x_163);
lean_dec(x_20);
x_164 = lean_ctor_get(x_21, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_165 = x_21;
} else {
 lean_dec_ref(x_21);
 x_165 = lean_box(0);
}
x_166 = l_Lean_mkAppN(x_11, x_163);
x_167 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__3;
x_168 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_167, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_unbox(x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_165);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_box(0);
x_173 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(x_2, x_166, x_167, x_164, x_163, x_172, x_3, x_4, x_5, x_6, x_7, x_8, x_171);
lean_dec(x_163);
lean_dec(x_164);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
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
lean_inc(x_2);
x_176 = l_Lean_Expr_mvar___override(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_176);
x_177 = lean_infer_type(x_176, x_5, x_6, x_7, x_8, x_174);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_166);
x_180 = lean_infer_type(x_166, x_5, x_6, x_7, x_8, x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_expr_dbg_to_string(x_176);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
x_185 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
if (lean_is_scalar(x_175)) {
 x_186 = lean_alloc_ctor(7, 2, 0);
} else {
 x_186 = x_175;
 lean_ctor_set_tag(x_186, 7);
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5;
if (lean_is_scalar(x_165)) {
 x_188 = lean_alloc_ctor(7, 2, 0);
} else {
 x_188 = x_165;
 lean_ctor_set_tag(x_188, 7);
}
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_MessageData_ofExpr(x_176);
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4;
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_MessageData_ofExpr(x_178);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6;
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
lean_inc(x_166);
x_197 = l_Lean_MessageData_ofExpr(x_166);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_191);
x_200 = l_Lean_MessageData_ofExpr(x_181);
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_185);
x_203 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_167, x_202, x_3, x_4, x_5, x_6, x_7, x_8, x_182);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(x_2, x_166, x_167, x_164, x_163, x_204, x_3, x_4, x_5, x_6, x_7, x_8, x_205);
lean_dec(x_204);
lean_dec(x_163);
lean_dec(x_164);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = lean_ctor_get(x_180, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_180, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_209 = x_180;
} else {
 lean_dec_ref(x_180);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_211 = lean_ctor_get(x_177, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_177, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_213 = x_177;
} else {
 lean_dec_ref(x_177);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_215 = !lean_is_exclusive(x_19);
if (x_215 == 0)
{
return x_19;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_19, 0);
x_217 = lean_ctor_get(x_19, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_19);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_219 = !lean_is_exclusive(x_13);
if (x_219 == 0)
{
return x_13;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_13, 0);
x_221 = lean_ctor_get(x_13, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_13);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_223 = !lean_is_exclusive(x_10);
if (x_223 == 0)
{
return x_10;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_10, 0);
x_225 = lean_ctor_get(x_10, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_10);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3), 9, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_1);
x_11 = l_Lean_commitWhen___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePendingInstMVar_x27___spec__1(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeSomeUsingDefault_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
return x_22;
}
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
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingInstances(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_List_isEmpty___rarg(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_9);
x_14 = lean_box(0);
x_15 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending___lambda__1(x_11, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = l_List_isEmpty___rarg(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending___lambda__1(x_18, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
return x_22;
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeSomeUsingDefault_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_12);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeSomeUsingDefault_x3f(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_free_object(x_1);
lean_dec(x_12);
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
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_18, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_19, 0, x_1);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
lean_ctor_set(x_1, 1, x_30);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_34 = x_19;
} else {
 lean_dec_ref(x_19);
 x_34 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_33);
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 1, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_1);
lean_dec(x_12);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
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
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_14, 0);
lean_dec(x_42);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_14, 0, x_43);
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_13);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
return x_14;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_14, 0);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_14);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_51);
x_53 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeSomeUsingDefault_x3f(x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_51);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_64 = x_57;
} else {
 lean_dec_ref(x_57);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_58, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_66 = x_58;
} else {
 lean_dec_ref(x_58);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_51);
lean_ctor_set(x_67, 1, x_65);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_51);
x_70 = lean_ctor_get(x_57, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_57, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
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
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_ctor_get(x_53, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_75 = x_53;
} else {
 lean_dec_ref(x_53);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_52);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_53, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_53, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_80 = x_53;
} else {
 lean_dec_ref(x_53);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getDefaultInstances___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizePending___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_16;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_9 = x_19;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
x_27 = lean_ctor_get(x_8, 2);
x_28 = lean_ctor_get(x_8, 3);
x_29 = lean_ctor_get(x_8, 4);
x_30 = lean_ctor_get(x_8, 5);
x_31 = lean_ctor_get(x_8, 6);
x_32 = lean_ctor_get(x_8, 7);
x_33 = lean_ctor_get(x_8, 8);
x_34 = lean_ctor_get(x_8, 9);
x_35 = lean_ctor_get(x_8, 10);
x_36 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_37 = lean_ctor_get(x_8, 11);
x_38 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
x_39 = l_Lean_replaceRef(x_24, x_30);
lean_dec(x_24);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_40 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_26);
lean_ctor_set(x_40, 2, x_27);
lean_ctor_set(x_40, 3, x_28);
lean_ctor_set(x_40, 4, x_29);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_31);
lean_ctor_set(x_40, 7, x_32);
lean_ctor_set(x_40, 8, x_33);
lean_ctor_set(x_40, 9, x_34);
lean_ctor_set(x_40, 10, x_35);
lean_ctor_set(x_40, 11, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*12, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*12 + 1, x_38);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_15);
x_41 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(x_15, x_1, x_4, x_5, x_6, x_7, x_40, x_9, x_23);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_16;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_9 = x_44;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_st_ref_take(x_5, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_48, 2);
lean_dec(x_51);
x_52 = l_List_reverse___rarg(x_16);
x_53 = l_List_appendTR___rarg(x_52, x_3);
lean_ctor_set(x_48, 2, x_53);
x_54 = lean_st_ref_set(x_5, x_48, x_49);
lean_dec(x_5);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_63 = lean_ctor_get(x_48, 0);
x_64 = lean_ctor_get(x_48, 1);
x_65 = lean_ctor_get(x_48, 3);
x_66 = lean_ctor_get(x_48, 4);
x_67 = lean_ctor_get(x_48, 5);
x_68 = lean_ctor_get(x_48, 6);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_48);
x_69 = l_List_reverse___rarg(x_16);
x_70 = l_List_appendTR___rarg(x_69, x_3);
x_71 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_64);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_65);
lean_ctor_set(x_71, 4, x_66);
lean_ctor_set(x_71, 5, x_67);
lean_ctor_set(x_71, 6, x_68);
x_72 = lean_st_ref_set(x_5, x_71, x_49);
lean_dec(x_5);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = 1;
x_76 = lean_box(x_75);
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
else
{
uint8_t x_78; 
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_41);
if (x_78 == 0)
{
return x_41;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_41, 0);
x_80 = lean_ctor_get(x_41, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_41);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_22);
lean_dec(x_21);
x_82 = lean_ctor_get(x_17, 1);
lean_inc(x_82);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_16;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_9 = x_82;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_10 = _tmp_9;
}
goto _start;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_2, 0);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_2);
x_86 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(x_84, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_3);
x_2 = x_85;
x_3 = x_89;
x_10 = x_88;
goto _start;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
lean_dec(x_87);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_92);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_dec(x_86);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_ctor_get(x_8, 0);
x_96 = lean_ctor_get(x_8, 1);
x_97 = lean_ctor_get(x_8, 2);
x_98 = lean_ctor_get(x_8, 3);
x_99 = lean_ctor_get(x_8, 4);
x_100 = lean_ctor_get(x_8, 5);
x_101 = lean_ctor_get(x_8, 6);
x_102 = lean_ctor_get(x_8, 7);
x_103 = lean_ctor_get(x_8, 8);
x_104 = lean_ctor_get(x_8, 9);
x_105 = lean_ctor_get(x_8, 10);
x_106 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_107 = lean_ctor_get(x_8, 11);
x_108 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
x_109 = l_Lean_replaceRef(x_94, x_100);
lean_dec(x_94);
lean_inc(x_107);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
x_110 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_96);
lean_ctor_set(x_110, 2, x_97);
lean_ctor_set(x_110, 3, x_98);
lean_ctor_set(x_110, 4, x_99);
lean_ctor_set(x_110, 5, x_109);
lean_ctor_set(x_110, 6, x_101);
lean_ctor_set(x_110, 7, x_102);
lean_ctor_set(x_110, 8, x_103);
lean_ctor_set(x_110, 9, x_104);
lean_ctor_set(x_110, 10, x_105);
lean_ctor_set(x_110, 11, x_107);
lean_ctor_set_uint8(x_110, sizeof(void*)*12, x_106);
lean_ctor_set_uint8(x_110, sizeof(void*)*12 + 1, x_108);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_84);
x_111 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio(x_84, x_1, x_4, x_5, x_6, x_7, x_110, x_9, x_93);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_84);
lean_ctor_set(x_115, 1, x_3);
x_2 = x_85;
x_3 = x_115;
x_10 = x_114;
goto _start;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_84);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
lean_dec(x_111);
x_118 = lean_st_ref_take(x_5, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_119, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 5);
lean_inc(x_125);
x_126 = lean_ctor_get(x_119, 6);
lean_inc(x_126);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 lean_ctor_release(x_119, 3);
 lean_ctor_release(x_119, 4);
 lean_ctor_release(x_119, 5);
 lean_ctor_release(x_119, 6);
 x_127 = x_119;
} else {
 lean_dec_ref(x_119);
 x_127 = lean_box(0);
}
x_128 = l_List_reverse___rarg(x_85);
x_129 = l_List_appendTR___rarg(x_128, x_3);
if (lean_is_scalar(x_127)) {
 x_130 = lean_alloc_ctor(0, 7, 0);
} else {
 x_130 = x_127;
}
lean_ctor_set(x_130, 0, x_121);
lean_ctor_set(x_130, 1, x_122);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_123);
lean_ctor_set(x_130, 4, x_124);
lean_ctor_set(x_130, 5, x_125);
lean_ctor_set(x_130, 6, x_126);
x_131 = lean_st_ref_set(x_5, x_130, x_120);
lean_dec(x_5);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
x_134 = 1;
x_135 = lean_box(x_134);
if (lean_is_scalar(x_133)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_133;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_132);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_137 = lean_ctor_get(x_111, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_111, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_139 = x_111;
} else {
 lean_dec_ref(x_111);
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
lean_dec(x_92);
lean_dec(x_91);
x_141 = lean_ctor_get(x_86, 1);
lean_inc(x_141);
lean_dec(x_86);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_84);
lean_ctor_set(x_142, 1, x_3);
x_2 = x_85;
x_3 = x_142;
x_10 = x_141;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_List_reverse___rarg(x_12);
x_14 = lean_box(0);
x_15 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio_visit(x_1, x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSomeUsingDefaultPrio(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
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
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_1);
{
lean_object* _tmp_1 = x_15;
lean_object* _tmp_2 = x_1;
lean_object* _tmp_9 = x_26;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_10 = _tmp_9;
}
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__3;
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__3;
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
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
else
{
uint8_t x_38; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1;
x_12 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___spec__1(x_11, x_9, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_12, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
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
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeclass instance problem is stuck, it is often due to metavariables", 69, 69);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_getMVarDecl(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_st_ref_get(x_8, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 5);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_MessageLog_hasErrors(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_14);
x_20 = lean_ctor_get(x_12, 2);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_Lean_indentExpr(x_20);
x_22 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_21);
lean_ctor_set(x_10, 0, x_22);
x_23 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_27;
}
else
{
lean_object* x_28; 
lean_free_object(x_10);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_box(0);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_ctor_get(x_29, 5);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_MessageLog_hasErrors(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_12, 2);
lean_inc(x_33);
lean_dec(x_12);
x_34 = l_Lean_indentExpr(x_33);
x_35 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_34);
lean_ctor_set(x_10, 0, x_35);
x_36 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_free_object(x_10);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_30);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_st_ref_get(x_8, x_44);
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
x_49 = lean_ctor_get(x_46, 5);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l_Lean_MessageLog_hasErrors(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_48);
x_51 = lean_ctor_get(x_43, 2);
lean_inc(x_51);
lean_dec(x_43);
x_52 = l_Lean_indentExpr(x_51);
x_53 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_2);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_59 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_43);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_48;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_47);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to create type class instance for", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = lean_infer_type(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getMVarDecl(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_indentExpr(x_20);
x_22 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__2;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_21);
lean_ctor_set(x_16, 0, x_22);
x_23 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_26, x_4, x_14, x_1, x_5, x_25, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_25);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_MessageData_ofFormat(x_30);
lean_ctor_set(x_3, 0, x_31);
x_32 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_3, x_4, x_14, x_1, x_5, x_25, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_25);
lean_dec(x_3);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
lean_dec(x_3);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_36, x_4, x_14, x_1, x_5, x_25, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_25);
lean_dec(x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_indentExpr(x_40);
x_42 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__2;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
x_48 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_47, x_4, x_14, x_1, x_5, x_46, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_50 = x_3;
} else {
 lean_dec_ref(x_3);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = l_Lean_MessageData_ofFormat(x_51);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_53, x_4, x_14, x_1, x_5, x_46, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_46);
lean_dec(x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
return x_13;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_13, 0);
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_13);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = lean_apply_8(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
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
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.reportStuckSyntheticMVar", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1;
x_2 = l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1;
x_3 = lean_unsigned_to_nat(229u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_7, 5);
x_26 = l_Lean_replaceRef(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
lean_ctor_set(x_7, 5, x_26);
switch (lean_obj_tag(x_23)) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_10);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Elab_Term_extraMsgToMsg(x_27);
lean_dec(x_27);
lean_inc(x_1);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___boxed), 9, 2);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_28);
x_30 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_box(0);
lean_ctor_set(x_10, 0, x_31);
return x_10;
}
}
case 1:
{
lean_object* x_32; 
lean_free_object(x_10);
x_32 = lean_ctor_get(x_23, 4);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_23, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_23, 3);
lean_inc(x_36);
lean_dec(x_23);
lean_inc(x_1);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___boxed), 12, 5);
lean_closure_set(x_37, 0, x_35);
lean_closure_set(x_37, 1, x_1);
lean_closure_set(x_37, 2, x_33);
lean_closure_set(x_37, 3, x_34);
lean_closure_set(x_37, 4, x_36);
x_38 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_23, 2);
lean_inc(x_40);
lean_dec(x_23);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
lean_inc(x_1);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__3___boxed), 11, 4);
lean_closure_set(x_42, 0, x_41);
lean_closure_set(x_42, 1, x_1);
lean_closure_set(x_42, 2, x_39);
lean_closure_set(x_42, 3, x_40);
x_43 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_43;
}
}
default: 
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_23);
lean_free_object(x_10);
lean_dec(x_1);
x_44 = l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2;
x_45 = l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
x_48 = lean_ctor_get(x_7, 2);
x_49 = lean_ctor_get(x_7, 3);
x_50 = lean_ctor_get(x_7, 4);
x_51 = lean_ctor_get(x_7, 5);
x_52 = lean_ctor_get(x_7, 6);
x_53 = lean_ctor_get(x_7, 7);
x_54 = lean_ctor_get(x_7, 8);
x_55 = lean_ctor_get(x_7, 9);
x_56 = lean_ctor_get(x_7, 10);
x_57 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_58 = lean_ctor_get(x_7, 11);
x_59 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_58);
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
lean_dec(x_7);
x_60 = l_Lean_replaceRef(x_22, x_51);
lean_dec(x_51);
lean_dec(x_22);
x_61 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_47);
lean_ctor_set(x_61, 2, x_48);
lean_ctor_set(x_61, 3, x_49);
lean_ctor_set(x_61, 4, x_50);
lean_ctor_set(x_61, 5, x_60);
lean_ctor_set(x_61, 6, x_52);
lean_ctor_set(x_61, 7, x_53);
lean_ctor_set(x_61, 8, x_54);
lean_ctor_set(x_61, 9, x_55);
lean_ctor_set(x_61, 10, x_56);
lean_ctor_set(x_61, 11, x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*12, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*12 + 1, x_59);
switch (lean_obj_tag(x_23)) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_10);
x_62 = lean_ctor_get(x_23, 0);
lean_inc(x_62);
lean_dec(x_23);
x_63 = l_Lean_Elab_Term_extraMsgToMsg(x_62);
lean_dec(x_62);
lean_inc(x_1);
x_64 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___boxed), 9, 2);
lean_closure_set(x_64, 0, x_1);
lean_closure_set(x_64, 1, x_63);
x_65 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_64, x_3, x_4, x_5, x_6, x_61, x_8, x_19);
return x_65;
}
else
{
lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = lean_box(0);
lean_ctor_set(x_10, 0, x_66);
return x_10;
}
}
case 1:
{
lean_object* x_67; 
lean_free_object(x_10);
x_67 = lean_ctor_get(x_23, 4);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_23, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_23, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_23, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_23, 3);
lean_inc(x_71);
lean_dec(x_23);
lean_inc(x_1);
x_72 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___boxed), 12, 5);
lean_closure_set(x_72, 0, x_70);
lean_closure_set(x_72, 1, x_1);
lean_closure_set(x_72, 2, x_68);
lean_closure_set(x_72, 3, x_69);
lean_closure_set(x_72, 4, x_71);
x_73 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_72, x_3, x_4, x_5, x_6, x_61, x_8, x_19);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_23, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_23, 2);
lean_inc(x_75);
lean_dec(x_23);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
lean_dec(x_67);
lean_inc(x_1);
x_77 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__3___boxed), 11, 4);
lean_closure_set(x_77, 0, x_76);
lean_closure_set(x_77, 1, x_1);
lean_closure_set(x_77, 2, x_74);
lean_closure_set(x_77, 3, x_75);
x_78 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_77, x_3, x_4, x_5, x_6, x_61, x_8, x_19);
return x_78;
}
}
default: 
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_23);
lean_free_object(x_10);
lean_dec(x_1);
x_79 = l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2;
x_80 = l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(x_79, x_3, x_4, x_5, x_6, x_61, x_8, x_19);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_81 = lean_ctor_get(x_10, 1);
lean_inc(x_81);
lean_dec(x_10);
x_82 = lean_ctor_get(x_11, 0);
lean_inc(x_82);
lean_dec(x_11);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_7, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_7, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_7, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_7, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_7, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_7, 5);
lean_inc(x_90);
x_91 = lean_ctor_get(x_7, 6);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 7);
lean_inc(x_92);
x_93 = lean_ctor_get(x_7, 8);
lean_inc(x_93);
x_94 = lean_ctor_get(x_7, 9);
lean_inc(x_94);
x_95 = lean_ctor_get(x_7, 10);
lean_inc(x_95);
x_96 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_97 = lean_ctor_get(x_7, 11);
lean_inc(x_97);
x_98 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
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
 lean_ctor_release(x_7, 9);
 lean_ctor_release(x_7, 10);
 lean_ctor_release(x_7, 11);
 x_99 = x_7;
} else {
 lean_dec_ref(x_7);
 x_99 = lean_box(0);
}
x_100 = l_Lean_replaceRef(x_83, x_90);
lean_dec(x_90);
lean_dec(x_83);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 12, 2);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_85);
lean_ctor_set(x_101, 1, x_86);
lean_ctor_set(x_101, 2, x_87);
lean_ctor_set(x_101, 3, x_88);
lean_ctor_set(x_101, 4, x_89);
lean_ctor_set(x_101, 5, x_100);
lean_ctor_set(x_101, 6, x_91);
lean_ctor_set(x_101, 7, x_92);
lean_ctor_set(x_101, 8, x_93);
lean_ctor_set(x_101, 9, x_94);
lean_ctor_set(x_101, 10, x_95);
lean_ctor_set(x_101, 11, x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*12, x_96);
lean_ctor_set_uint8(x_101, sizeof(void*)*12 + 1, x_98);
switch (lean_obj_tag(x_84)) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_84, 0);
lean_inc(x_102);
lean_dec(x_84);
x_103 = l_Lean_Elab_Term_extraMsgToMsg(x_102);
lean_dec(x_102);
lean_inc(x_1);
x_104 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___boxed), 9, 2);
lean_closure_set(x_104, 0, x_1);
lean_closure_set(x_104, 1, x_103);
x_105 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_104, x_3, x_4, x_5, x_6, x_101, x_8, x_81);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_101);
lean_dec(x_84);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_81);
return x_107;
}
}
case 1:
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_84, 4);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_84, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_84, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_84, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_84, 3);
lean_inc(x_112);
lean_dec(x_84);
lean_inc(x_1);
x_113 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___boxed), 12, 5);
lean_closure_set(x_113, 0, x_111);
lean_closure_set(x_113, 1, x_1);
lean_closure_set(x_113, 2, x_109);
lean_closure_set(x_113, 3, x_110);
lean_closure_set(x_113, 4, x_112);
x_114 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_113, x_3, x_4, x_5, x_6, x_101, x_8, x_81);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_84, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_84, 2);
lean_inc(x_116);
lean_dec(x_84);
x_117 = lean_ctor_get(x_108, 0);
lean_inc(x_117);
lean_dec(x_108);
lean_inc(x_1);
x_118 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__3___boxed), 11, 4);
lean_closure_set(x_118, 0, x_117);
lean_closure_set(x_118, 1, x_1);
lean_closure_set(x_118, 2, x_115);
lean_closure_set(x_118, 3, x_116);
x_119 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_118, x_3, x_4, x_5, x_6, x_101, x_8, x_81);
return x_119;
}
}
default: 
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_84);
lean_dec(x_1);
x_120 = l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2;
x_121 = l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(x_120, x_3, x_4, x_5, x_6, x_101, x_8, x_81);
return x_121;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_reportStuckSyntheticMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_Term_reportStuckSyntheticMVar(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Elab_Term_reportStuckSyntheticMVar(x_16, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_5 = x_17;
x_6 = x_20;
x_7 = lean_box(0);
x_14 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_10, 2);
x_14 = lean_box(0);
lean_ctor_set(x_10, 2, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_box(0);
lean_inc(x_13);
x_19 = l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(x_1, x_13, x_17, x_13, x_13, x_18, lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
x_30 = lean_ctor_get(x_10, 2);
x_31 = lean_ctor_get(x_10, 3);
x_32 = lean_ctor_get(x_10, 4);
x_33 = lean_ctor_get(x_10, 5);
x_34 = lean_ctor_get(x_10, 6);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
lean_ctor_set(x_36, 6, x_34);
x_37 = lean_st_ref_set(x_3, x_36, x_11);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = lean_box(0);
lean_inc(x_30);
x_41 = l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(x_1, x_30, x_39, x_30, x_30, x_40, lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_30);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_47 = x_41;
} else {
 lean_dec_ref(x_41);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
{
lean_object* _tmp_4 = x_17;
lean_object* _tmp_5 = x_3;
lean_object* _tmp_6 = lean_box(0);
lean_object* _tmp_13 = x_20;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_14 = _tmp_13;
}
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_18, 1);
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_dec(x_28);
x_29 = 0;
x_30 = l_Lean_Syntax_getPos_x3f(x_27, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_free_object(x_22);
lean_dec(x_27);
lean_free_object(x_18);
lean_inc(x_3);
{
lean_object* _tmp_4 = x_17;
lean_object* _tmp_5 = x_3;
lean_object* _tmp_6 = lean_box(0);
lean_object* _tmp_13 = x_24;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_14 = _tmp_13;
}
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_ctor_set(x_30, 0, x_27);
x_34 = lean_box(0);
lean_ctor_set(x_22, 1, x_34);
lean_ctor_set(x_22, 0, x_30);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_27);
x_36 = lean_box(0);
lean_ctor_set(x_22, 1, x_36);
lean_ctor_set(x_22, 0, x_35);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
lean_dec(x_22);
x_38 = 0;
x_39 = l_Lean_Syntax_getPos_x3f(x_37, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_37);
lean_free_object(x_18);
lean_inc(x_3);
{
lean_object* _tmp_4 = x_17;
lean_object* _tmp_5 = x_3;
lean_object* _tmp_6 = lean_box(0);
lean_object* _tmp_13 = x_24;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_14 = _tmp_13;
}
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_3);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_37);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_18, 0, x_44);
return x_18;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_dec(x_18);
x_46 = lean_ctor_get(x_22, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_47 = x_22;
} else {
 lean_dec_ref(x_22);
 x_47 = lean_box(0);
}
x_48 = 0;
x_49 = l_Lean_Syntax_getPos_x3f(x_46, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_dec(x_47);
lean_dec(x_46);
lean_inc(x_3);
{
lean_object* _tmp_4 = x_17;
lean_object* _tmp_5 = x_3;
lean_object* _tmp_6 = lean_box(0);
lean_object* _tmp_13 = x_45;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_14 = _tmp_13;
}
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_3);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_46);
x_53 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_47;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
return x_55;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1;
x_14 = l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1(x_11, x_12, x_13, x_12, x_12, x_13, lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__1;
x_19 = lean_box(0);
x_20 = lean_apply_8(x_18, x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_level_eq(x_6, x_8);
if (x_10 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = lean_level_eq(x_7, x_9);
if (x_12 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__4___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = 32;
x_8 = 16;
x_9 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_sub(x_9, x_10);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = l_Lean_Level_hash(x_12);
lean_dec(x_12);
x_15 = l_Lean_Level_hash(x_13);
lean_dec(x_13);
x_16 = lean_uint64_mix_hash(x_14, x_15);
x_17 = lean_uint64_shift_right(x_16, x_7);
x_18 = lean_uint64_xor(x_16, x_17);
x_19 = lean_uint64_shift_right(x_18, x_8);
x_20 = lean_uint64_xor(x_18, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_land(x_21, x_11);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_array_get_size(x_1);
x_30 = 32;
x_31 = 16;
x_32 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_33 = 1;
x_34 = lean_usize_sub(x_32, x_33);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
x_37 = l_Lean_Level_hash(x_35);
lean_dec(x_35);
x_38 = l_Lean_Level_hash(x_36);
lean_dec(x_36);
x_39 = lean_uint64_mix_hash(x_37, x_38);
x_40 = lean_uint64_shift_right(x_39, x_30);
x_41 = lean_uint64_xor(x_39, x_40);
x_42 = lean_uint64_shift_right(x_41, x_31);
x_43 = lean_uint64_xor(x_41, x_42);
x_44 = lean_uint64_to_usize(x_43);
x_45 = lean_usize_land(x_44, x_34);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__4___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_9, x_8);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_uget(x_7, x_9);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 0);
lean_dec(x_23);
lean_inc(x_22);
x_24 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7(x_1, x_2, x_3, x_20, x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_10, 0, x_28);
lean_ctor_set(x_24, 0, x_10);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_10, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_22);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_6);
x_34 = 1;
x_35 = lean_usize_add(x_9, x_34);
x_9 = x_35;
x_17 = x_32;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_dec(x_10);
lean_inc(x_37);
x_38 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7(x_1, x_2, x_3, x_20, x_37, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_6);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_inc(x_6);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = lean_usize_add(x_9, x_48);
x_9 = x_49;
x_10 = x_47;
x_17 = x_45;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
x_18 = l_Lean_Level_hash(x_3);
lean_dec(x_3);
x_19 = l_Lean_Level_hash(x_4);
lean_dec(x_4);
x_20 = lean_uint64_mix_hash(x_18, x_19);
x_21 = 32;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = 16;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_29 = 1;
x_30 = lean_usize_sub(x_28, x_29);
x_31 = lean_usize_land(x_27, x_30);
x_32 = lean_array_uget(x_16, x_31);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1(x_14, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_35 = lean_ctor_get(x_2, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_2, 0);
lean_dec(x_36);
x_37 = lean_array_push(x_5, x_1);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_15, x_38);
lean_dec(x_15);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_32);
x_42 = lean_array_uset(x_16, x_31, x_41);
x_43 = lean_unsigned_to_nat(4u);
x_44 = lean_nat_mul(x_39, x_43);
x_45 = lean_unsigned_to_nat(3u);
x_46 = lean_nat_div(x_44, x_45);
lean_dec(x_44);
x_47 = lean_array_get_size(x_42);
x_48 = lean_nat_dec_le(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__2(x_42);
lean_ctor_set(x_2, 1, x_49);
lean_ctor_set(x_2, 0, x_39);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_37);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_13);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_ctor_set(x_2, 1, x_42);
lean_ctor_set(x_2, 0, x_39);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_37);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_13);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_2);
x_56 = lean_array_push(x_5, x_1);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_15, x_57);
lean_dec(x_15);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_14);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_32);
x_61 = lean_array_uset(x_16, x_31, x_60);
x_62 = lean_unsigned_to_nat(4u);
x_63 = lean_nat_mul(x_58, x_62);
x_64 = lean_unsigned_to_nat(3u);
x_65 = lean_nat_div(x_63, x_64);
lean_dec(x_63);
x_66 = lean_array_get_size(x_61);
x_67 = lean_nat_dec_le(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__2(x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_56);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_13);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_58);
lean_ctor_set(x_73, 1, x_61);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_56);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_13);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_2);
lean_ctor_set(x_77, 1, x_5);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_13);
return x_79;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_8, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_27; 
x_19 = lean_array_uget(x_6, x_8);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_9, 1);
x_29 = lean_ctor_get(x_9, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_19, 2);
lean_inc(x_33);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Level_normLtAux(x_33, x_34, x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_box(0);
x_37 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(x_19, x_30, x_32, x_33, x_31, x_36, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_41);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_38, 0, x_9);
x_20 = x_38;
x_21 = x_39;
goto block_26;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_42);
lean_ctor_set(x_9, 0, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_9);
x_20 = x_43;
x_21 = x_39;
goto block_26;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_box(0);
x_45 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(x_19, x_30, x_33, x_32, x_31, x_44, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_49);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_46, 0, x_9);
x_20 = x_46;
x_21 = x_47;
goto block_26;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
lean_dec(x_46);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_50);
lean_ctor_set(x_9, 0, x_5);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_9);
x_20 = x_51;
x_21 = x_47;
goto block_26;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
lean_dec(x_9);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_19, 2);
lean_inc(x_56);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Level_normLtAux(x_56, x_57, x_55, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_box(0);
x_60 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(x_19, x_53, x_55, x_56, x_54, x_59, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
lean_inc(x_5);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_5);
lean_ctor_set(x_65, 1, x_63);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
x_20 = x_66;
x_21 = x_62;
goto block_26;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_box(0);
x_68 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(x_19, x_53, x_56, x_55, x_54, x_67, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
lean_inc(x_5);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_71);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
x_20 = x_74;
x_21 = x_70;
goto block_26;
}
}
block_26:
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_8, x_23);
x_8 = x_24;
x_9 = x_22;
x_16 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_array_size(x_13);
x_18 = 0;
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__8(x_1, x_2, x_3, x_13, x_14, x_15, x_13, x_17, x_18, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___lambda__1(x_23, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
x_36 = lean_array_size(x_32);
x_37 = 0;
x_38 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(x_1, x_2, x_32, x_33, x_34, x_32, x_36, x_37, x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___lambda__1(x_42, x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_39);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_8, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_27; 
x_19 = lean_array_uget(x_6, x_8);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_9, 1);
x_29 = lean_ctor_get(x_9, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_19, 2);
lean_inc(x_33);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Level_normLtAux(x_33, x_34, x_32, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_box(0);
x_37 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(x_19, x_30, x_32, x_33, x_31, x_36, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_41);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_38, 0, x_9);
x_20 = x_38;
x_21 = x_39;
goto block_26;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_42);
lean_ctor_set(x_9, 0, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_9);
x_20 = x_43;
x_21 = x_39;
goto block_26;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_box(0);
x_45 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(x_19, x_30, x_33, x_32, x_31, x_44, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_49);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_46, 0, x_9);
x_20 = x_46;
x_21 = x_47;
goto block_26;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
lean_dec(x_46);
lean_inc(x_5);
lean_ctor_set(x_9, 1, x_50);
lean_ctor_set(x_9, 0, x_5);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_9);
x_20 = x_51;
x_21 = x_47;
goto block_26;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
lean_dec(x_9);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_19, 2);
lean_inc(x_56);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Level_normLtAux(x_56, x_57, x_55, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_box(0);
x_60 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(x_19, x_53, x_55, x_56, x_54, x_59, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
lean_inc(x_5);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_5);
lean_ctor_set(x_65, 1, x_63);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
x_20 = x_66;
x_21 = x_62;
goto block_26;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = lean_box(0);
x_68 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(x_19, x_53, x_56, x_55, x_54, x_67, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
lean_inc(x_5);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_71);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
x_20 = x_74;
x_21 = x_70;
goto block_26;
}
}
block_26:
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_8, x_23);
x_8 = x_24;
x_9 = x_22;
x_16 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_13 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7(x_1, x_2, x_4, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_array_size(x_24);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10(x_1, x_2, x_23, x_24, x_25, x_24, x_27, x_28, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stuck at solving universe constraint", 36, 36);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_nat_dec_lt(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_17 = l_Lean_Meta_instInhabitedPostponedEntry;
x_18 = lean_array_get(x_17, x_1, x_4);
x_19 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore(x_19, x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_fget(x_1, x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 2;
x_26 = 0;
lean_inc(x_11);
x_27 = l_Lean_logAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__8(x_24, x_21, x_25, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_nat_add(x_4, x_29);
lean_dec(x_4);
x_31 = lean_box(0);
x_3 = x_31;
x_4 = x_30;
x_5 = lean_box(0);
x_6 = lean_box(0);
x_13 = x_28;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_26 = lean_ctor_get(x_7, 11);
x_27 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_28 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_29, 2, x_16);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_18);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_29, 6, x_20);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_23);
lean_ctor_set(x_29, 10, x_24);
lean_ctor_set(x_29, 11, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*12, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*12 + 1, x_27);
x_30 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_9);
lean_dec(x_29);
return x_30;
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_instBEq;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_instHashable;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__3;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = l_Lean_Meta_getPostponed___rarg(x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1;
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2;
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4;
x_14 = l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6(x_11, x_12, x_9, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11(x_17, x_20, x_21, x_19, lean_box(0), lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_instInhabitedPostponedEntry;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get(x_24, x_17, x_25);
lean_dec(x_17);
x_27 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_26);
x_28 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore(x_27, x_26, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(x_31, x_29, x_1, x_2, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
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
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_22);
if (x_37 == 0)
{
return x_22;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__8___boxed(lean_object** _args) {
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
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_20 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_forIn___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseContraints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Meta_processPostponed(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseContraints___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseContraints(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Lean_Name_quickCmp(x_1, x_6);
switch (x_9) {
case 0:
{
uint8_t x_10; 
x_10 = l_Lean_RBNode_isBlack___rarg(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(x_1, x_5);
x_12 = 0;
lean_ctor_set(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(x_1, x_5);
x_14 = l_Lean_RBNode_balLeft___rarg(x_13, x_6, x_7, x_8);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_15 = l_Lean_RBNode_appendTrees___rarg(x_5, x_8);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___rarg(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(x_1, x_8);
x_18 = 0;
lean_ctor_set(x_2, 3, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(x_1, x_8);
x_20 = l_Lean_RBNode_balRight___rarg(x_5, x_6, x_7, x_19);
return x_20;
}
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_25 = l_Lean_Name_quickCmp(x_1, x_22);
switch (x_25) {
case 0:
{
uint8_t x_26; 
x_26 = l_Lean_RBNode_isBlack___rarg(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(x_1, x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(x_1, x_21);
x_31 = l_Lean_RBNode_balLeft___rarg(x_30, x_22, x_23, x_24);
return x_31;
}
}
case 1:
{
lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_22);
x_32 = l_Lean_RBNode_appendTrees___rarg(x_21, x_24);
return x_32;
}
default: 
{
uint8_t x_33; 
x_33 = l_Lean_RBNode_isBlack___rarg(x_24);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(x_1, x_24);
x_35 = 0;
x_36 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(x_1, x_24);
x_38 = l_Lean_RBNode_balRight___rarg(x_21, x_22, x_23, x_37);
return x_38;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_RBNode_erase___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__1(x_1, x_13);
lean_ctor_set(x_10, 1, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
x_27 = lean_ctor_get(x_10, 5);
x_28 = lean_ctor_get(x_10, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_29 = l_Lean_RBNode_erase___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__1(x_1, x_23);
x_30 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set(x_30, 6, x_28);
x_31 = lean_st_ref_set(x_3, x_30, x_11);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Term_PostponeBehavior_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static uint8_t _init_l_Lean_Elab_Term_instInhabitedPostponeBehavior() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.PostponeBehavior.yes", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__3;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__6;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.PostponeBehavior.no", 34, 34);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__3;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__6;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Term.PostponeBehavior.partial", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__3;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__6;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__19;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158_(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__12;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__14;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
default: 
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__18;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__20;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_instReprPostponeBehavior___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_instReprPostponeBehavior() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instReprPostponeBehavior___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Elab_Term_PostponeBehavior_toCtorIdx(x_1);
x_4 = l_Lean_Elab_Term_PostponeBehavior_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_instBEqPostponeBehavior___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_instBEqPostponeBehavior() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instBEqPostponeBehavior___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_PostponeBehavior_ofBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_PostponeBehavior_ofBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Term_PostponeBehavior_ofBool(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not synthesize default value for parameter '", 50, 50);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' using tactics", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not synthesize default value for field '", 46, 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' of '", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_MessageData_ofName(x_12);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = 2;
x_19 = 0;
x_20 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_1, x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
default: 
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = l_Lean_MessageData_ofName(x_22);
x_25 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__6;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_25);
x_26 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__8;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofName(x_23);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = 2;
x_33 = 0;
x_34 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_1, x_31, x_32, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_2);
x_37 = l_Lean_MessageData_ofName(x_35);
x_38 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__6;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__8;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_MessageData_ofName(x_36);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = 2;
x_47 = 0;
x_48 = l_Lean_logAt___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__2(x_1, x_45, x_46, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_1, x_2, x_3);
x_12 = l_Lean_Elab_Term_withoutErrToSorryImp___rarg(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__1___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_1, x_2, x_3);
x_12 = l_Lean_Elab_Term_withoutErrToSorryImp___rarg(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__2___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___rarg), 10, 1);
lean_closure_set(x_13, 0, x_2);
x_14 = l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___rarg), 10, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___spec__2___rarg(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__6;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
x_24 = lean_ctor_get(x_8, 9);
x_25 = lean_ctor_get(x_8, 10);
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_27 = lean_ctor_get(x_8, 11);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
x_29 = l_Lean_replaceRef(x_12, x_20);
lean_dec(x_20);
lean_dec(x_12);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_29);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_ctor_set(x_8, 5, x_29);
x_30 = lean_nat_dec_eq(x_18, x_19);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_8);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_18, x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_16);
lean_ctor_set(x_33, 2, x_17);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_19);
lean_ctor_set(x_33, 5, x_29);
lean_ctor_set(x_33, 6, x_21);
lean_ctor_set(x_33, 7, x_22);
lean_ctor_set(x_33, 8, x_23);
lean_ctor_set(x_33, 9, x_24);
lean_ctor_set(x_33, 10, x_25);
lean_ctor_set(x_33, 11, x_27);
lean_ctor_set_uint8(x_33, sizeof(void*)*12, x_26);
lean_ctor_set_uint8(x_33, sizeof(void*)*12 + 1, x_28);
x_34 = lean_st_ref_get(x_5, x_13);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_36, 2);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_List_isEmpty___rarg(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_34);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_box(x_40);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_43, 0, x_41);
lean_closure_set(x_43, 1, x_42);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_44 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_40, x_40, x_4, x_5, x_6, x_7, x_33, x_9, x_37);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_44, 1);
x_49 = lean_ctor_get(x_44, 0);
lean_dec(x_49);
x_50 = 0;
x_51 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_50);
if (x_51 == 0)
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_44);
x_52 = 1;
x_53 = lean_box(x_52);
x_54 = lean_box(x_40);
x_55 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_55, 0, x_53);
lean_closure_set(x_55, 1, x_54);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_56 = l_Lean_Elab_Term_withoutPostponing___rarg(x_55, x_4, x_5, x_6, x_7, x_33, x_9, x_48);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_60 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_4, x_5, x_6, x_7, x_33, x_9, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_64 = l_Lean_Elab_Term_withoutPostponing___rarg(x_43, x_4, x_5, x_6, x_7, x_33, x_9, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_68 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_40, x_52, x_4, x_5, x_6, x_7, x_33, x_9, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_68, 1);
x_73 = lean_ctor_get(x_68, 0);
lean_dec(x_73);
x_74 = 1;
x_75 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_76 = lean_box(0);
lean_ctor_set(x_68, 0, x_76);
return x_68;
}
else
{
lean_object* x_77; 
lean_free_object(x_68);
x_77 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_4, x_5, x_6, x_7, x_33, x_9, x_72);
return x_77;
}
}
else
{
lean_object* x_78; uint8_t x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_dec(x_68);
x_79 = 1;
x_80 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
else
{
lean_object* x_83; 
x_83 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_4, x_5, x_6, x_7, x_33, x_9, x_78);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_68, 1);
lean_inc(x_84);
lean_dec(x_68);
x_85 = lean_box(0);
x_3 = x_85;
x_8 = x_33;
x_10 = x_84;
goto _start;
}
}
else
{
uint8_t x_87; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_87 = !lean_is_exclusive(x_68);
if (x_87 == 0)
{
return x_68;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_68, 0);
x_89 = lean_ctor_get(x_68, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_68);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_64, 1);
lean_inc(x_91);
lean_dec(x_64);
x_92 = lean_box(0);
x_3 = x_92;
x_8 = x_33;
x_10 = x_91;
goto _start;
}
}
else
{
uint8_t x_94; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_64);
if (x_94 == 0)
{
return x_64;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_64, 0);
x_96 = lean_ctor_get(x_64, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_64);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_43);
x_98 = lean_ctor_get(x_60, 1);
lean_inc(x_98);
lean_dec(x_60);
x_99 = lean_box(0);
x_3 = x_99;
x_8 = x_33;
x_10 = x_98;
goto _start;
}
}
else
{
uint8_t x_101; 
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_101 = !lean_is_exclusive(x_60);
if (x_101 == 0)
{
return x_60;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_60, 0);
x_103 = lean_ctor_get(x_60, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_60);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_43);
x_105 = lean_ctor_get(x_56, 1);
lean_inc(x_105);
lean_dec(x_56);
x_106 = lean_box(0);
x_3 = x_106;
x_8 = x_33;
x_10 = x_105;
goto _start;
}
}
else
{
uint8_t x_108; 
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_108 = !lean_is_exclusive(x_56);
if (x_108 == 0)
{
return x_56;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_56, 0);
x_110 = lean_ctor_get(x_56, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_56);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = lean_box(0);
lean_ctor_set(x_44, 0, x_112);
return x_44;
}
}
else
{
lean_object* x_113; uint8_t x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_44, 1);
lean_inc(x_113);
lean_dec(x_44);
x_114 = 0;
x_115 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_114);
if (x_115 == 0)
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = 1;
x_117 = lean_box(x_116);
x_118 = lean_box(x_40);
x_119 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_119, 0, x_117);
lean_closure_set(x_119, 1, x_118);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_120 = l_Lean_Elab_Term_withoutPostponing___rarg(x_119, x_4, x_5, x_6, x_7, x_33, x_9, x_113);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_124 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_4, x_5, x_6, x_7, x_33, x_9, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_128 = l_Lean_Elab_Term_withoutPostponing___rarg(x_43, x_4, x_5, x_6, x_7, x_33, x_9, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_132 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_40, x_116, x_4, x_5, x_6, x_7, x_33, x_9, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
x_137 = 1;
x_138 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_139 = lean_box(0);
if (lean_is_scalar(x_136)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_136;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_135);
return x_140;
}
else
{
lean_object* x_141; 
lean_dec(x_136);
x_141 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_4, x_5, x_6, x_7, x_33, x_9, x_135);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
lean_dec(x_132);
x_143 = lean_box(0);
x_3 = x_143;
x_8 = x_33;
x_10 = x_142;
goto _start;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_145 = lean_ctor_get(x_132, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_132, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_147 = x_132;
} else {
 lean_dec_ref(x_132);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_128, 1);
lean_inc(x_149);
lean_dec(x_128);
x_150 = lean_box(0);
x_3 = x_150;
x_8 = x_33;
x_10 = x_149;
goto _start;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_152 = lean_ctor_get(x_128, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_128, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_154 = x_128;
} else {
 lean_dec_ref(x_128);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_43);
x_156 = lean_ctor_get(x_124, 1);
lean_inc(x_156);
lean_dec(x_124);
x_157 = lean_box(0);
x_3 = x_157;
x_8 = x_33;
x_10 = x_156;
goto _start;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_159 = lean_ctor_get(x_124, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_124, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_161 = x_124;
} else {
 lean_dec_ref(x_124);
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
lean_object* x_163; lean_object* x_164; 
lean_dec(x_43);
x_163 = lean_ctor_get(x_120, 1);
lean_inc(x_163);
lean_dec(x_120);
x_164 = lean_box(0);
x_3 = x_164;
x_8 = x_33;
x_10 = x_163;
goto _start;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_166 = lean_ctor_get(x_120, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_120, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_168 = x_120;
} else {
 lean_dec_ref(x_120);
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
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_113);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_43);
x_172 = lean_ctor_get(x_44, 1);
lean_inc(x_172);
lean_dec(x_44);
x_173 = lean_box(0);
x_3 = x_173;
x_8 = x_33;
x_10 = x_172;
goto _start;
}
}
else
{
uint8_t x_175; 
lean_dec(x_43);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_175 = !lean_is_exclusive(x_44);
if (x_175 == 0)
{
return x_44;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_44, 0);
x_177 = lean_ctor_get(x_44, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_44);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_179 = lean_box(0);
lean_ctor_set(x_34, 0, x_179);
return x_34;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_180 = lean_ctor_get(x_34, 0);
x_181 = lean_ctor_get(x_34, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_34);
x_182 = lean_ctor_get(x_180, 2);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_List_isEmpty___rarg(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = 0;
x_185 = lean_box(x_184);
x_186 = lean_box(x_184);
x_187 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_187, 0, x_185);
lean_closure_set(x_187, 1, x_186);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_188 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_184, x_184, x_4, x_5, x_6, x_7, x_33, x_9, x_181);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; 
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
x_193 = 0;
x_194 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_193);
if (x_194 == 0)
{
uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_192);
x_195 = 1;
x_196 = lean_box(x_195);
x_197 = lean_box(x_184);
x_198 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_198, 0, x_196);
lean_closure_set(x_198, 1, x_197);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_199 = l_Lean_Elab_Term_withoutPostponing___rarg(x_198, x_4, x_5, x_6, x_7, x_33, x_9, x_191);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_unbox(x_200);
lean_dec(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_dec(x_199);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_203 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_4, x_5, x_6, x_7, x_33, x_9, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_unbox(x_204);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_dec(x_203);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_207 = l_Lean_Elab_Term_withoutPostponing___rarg(x_187, x_4, x_5, x_6, x_7, x_33, x_9, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
lean_dec(x_207);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_211 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_184, x_195, x_4, x_5, x_6, x_7, x_33, x_9, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_unbox(x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; 
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_215 = x_211;
} else {
 lean_dec_ref(x_211);
 x_215 = lean_box(0);
}
x_216 = 1;
x_217 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_218 = lean_box(0);
if (lean_is_scalar(x_215)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_215;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_214);
return x_219;
}
else
{
lean_object* x_220; 
lean_dec(x_215);
x_220 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_4, x_5, x_6, x_7, x_33, x_9, x_214);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_211, 1);
lean_inc(x_221);
lean_dec(x_211);
x_222 = lean_box(0);
x_3 = x_222;
x_8 = x_33;
x_10 = x_221;
goto _start;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_224 = lean_ctor_get(x_211, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_211, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_226 = x_211;
} else {
 lean_dec_ref(x_211);
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
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_207, 1);
lean_inc(x_228);
lean_dec(x_207);
x_229 = lean_box(0);
x_3 = x_229;
x_8 = x_33;
x_10 = x_228;
goto _start;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_231 = lean_ctor_get(x_207, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_207, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_233 = x_207;
} else {
 lean_dec_ref(x_207);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_187);
x_235 = lean_ctor_get(x_203, 1);
lean_inc(x_235);
lean_dec(x_203);
x_236 = lean_box(0);
x_3 = x_236;
x_8 = x_33;
x_10 = x_235;
goto _start;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_187);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_238 = lean_ctor_get(x_203, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_203, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_240 = x_203;
} else {
 lean_dec_ref(x_203);
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
lean_object* x_242; lean_object* x_243; 
lean_dec(x_187);
x_242 = lean_ctor_get(x_199, 1);
lean_inc(x_242);
lean_dec(x_199);
x_243 = lean_box(0);
x_3 = x_243;
x_8 = x_33;
x_10 = x_242;
goto _start;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_187);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_245 = lean_ctor_get(x_199, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_199, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_247 = x_199;
} else {
 lean_dec_ref(x_199);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_187);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_249 = lean_box(0);
if (lean_is_scalar(x_192)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_192;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_191);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_187);
x_251 = lean_ctor_get(x_188, 1);
lean_inc(x_251);
lean_dec(x_188);
x_252 = lean_box(0);
x_3 = x_252;
x_8 = x_33;
x_10 = x_251;
goto _start;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_187);
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_254 = lean_ctor_get(x_188, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_188, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_256 = x_188;
} else {
 lean_dec_ref(x_188);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_258 = lean_box(0);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_181);
return x_259;
}
}
}
else
{
lean_object* x_260; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_260 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1(x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_261 = lean_ctor_get(x_8, 0);
x_262 = lean_ctor_get(x_8, 1);
x_263 = lean_ctor_get(x_8, 2);
x_264 = lean_ctor_get(x_8, 3);
x_265 = lean_ctor_get(x_8, 4);
x_266 = lean_ctor_get(x_8, 5);
x_267 = lean_ctor_get(x_8, 6);
x_268 = lean_ctor_get(x_8, 7);
x_269 = lean_ctor_get(x_8, 8);
x_270 = lean_ctor_get(x_8, 9);
x_271 = lean_ctor_get(x_8, 10);
x_272 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_273 = lean_ctor_get(x_8, 11);
x_274 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_273);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_8);
x_275 = l_Lean_replaceRef(x_12, x_266);
lean_dec(x_266);
lean_dec(x_12);
lean_inc(x_273);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_275);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
x_276 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_276, 0, x_261);
lean_ctor_set(x_276, 1, x_262);
lean_ctor_set(x_276, 2, x_263);
lean_ctor_set(x_276, 3, x_264);
lean_ctor_set(x_276, 4, x_265);
lean_ctor_set(x_276, 5, x_275);
lean_ctor_set(x_276, 6, x_267);
lean_ctor_set(x_276, 7, x_268);
lean_ctor_set(x_276, 8, x_269);
lean_ctor_set(x_276, 9, x_270);
lean_ctor_set(x_276, 10, x_271);
lean_ctor_set(x_276, 11, x_273);
lean_ctor_set_uint8(x_276, sizeof(void*)*12, x_272);
lean_ctor_set_uint8(x_276, sizeof(void*)*12 + 1, x_274);
x_277 = lean_nat_dec_eq(x_264, x_265);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
lean_dec(x_276);
x_278 = lean_unsigned_to_nat(1u);
x_279 = lean_nat_add(x_264, x_278);
lean_dec(x_264);
x_280 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_280, 0, x_261);
lean_ctor_set(x_280, 1, x_262);
lean_ctor_set(x_280, 2, x_263);
lean_ctor_set(x_280, 3, x_279);
lean_ctor_set(x_280, 4, x_265);
lean_ctor_set(x_280, 5, x_275);
lean_ctor_set(x_280, 6, x_267);
lean_ctor_set(x_280, 7, x_268);
lean_ctor_set(x_280, 8, x_269);
lean_ctor_set(x_280, 9, x_270);
lean_ctor_set(x_280, 10, x_271);
lean_ctor_set(x_280, 11, x_273);
lean_ctor_set_uint8(x_280, sizeof(void*)*12, x_272);
lean_ctor_set_uint8(x_280, sizeof(void*)*12 + 1, x_274);
x_281 = lean_st_ref_get(x_5, x_13);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_284 = x_281;
} else {
 lean_dec_ref(x_281);
 x_284 = lean_box(0);
}
x_285 = lean_ctor_get(x_282, 2);
lean_inc(x_285);
lean_dec(x_282);
x_286 = l_List_isEmpty___rarg(x_285);
lean_dec(x_285);
if (x_286 == 0)
{
uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_284);
x_287 = 0;
x_288 = lean_box(x_287);
x_289 = lean_box(x_287);
x_290 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_290, 0, x_288);
lean_closure_set(x_290, 1, x_289);
lean_inc(x_9);
lean_inc(x_280);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_291 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_287, x_287, x_4, x_5, x_6, x_7, x_280, x_9, x_283);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_unbox(x_292);
lean_dec(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; uint8_t x_297; 
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_295 = x_291;
} else {
 lean_dec_ref(x_291);
 x_295 = lean_box(0);
}
x_296 = 0;
x_297 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_296);
if (x_297 == 0)
{
uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_295);
x_298 = 1;
x_299 = lean_box(x_298);
x_300 = lean_box(x_287);
x_301 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed), 9, 2);
lean_closure_set(x_301, 0, x_299);
lean_closure_set(x_301, 1, x_300);
lean_inc(x_9);
lean_inc(x_280);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_302 = l_Lean_Elab_Term_withoutPostponing___rarg(x_301, x_4, x_5, x_6, x_7, x_280, x_9, x_294);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; uint8_t x_304; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_unbox(x_303);
lean_dec(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_302, 1);
lean_inc(x_305);
lean_dec(x_302);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_306 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_4, x_5, x_6, x_7, x_280, x_9, x_305);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; uint8_t x_308; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_unbox(x_307);
lean_dec(x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_dec(x_306);
lean_inc(x_9);
lean_inc(x_280);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_310 = l_Lean_Elab_Term_withoutPostponing___rarg(x_290, x_4, x_5, x_6, x_7, x_280, x_9, x_309);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_unbox(x_311);
lean_dec(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_310, 1);
lean_inc(x_313);
lean_dec(x_310);
lean_inc(x_9);
lean_inc(x_280);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_314 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_287, x_298, x_4, x_5, x_6, x_7, x_280, x_9, x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; uint8_t x_316; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_unbox(x_315);
lean_dec(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; uint8_t x_320; 
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_318 = x_314;
} else {
 lean_dec_ref(x_314);
 x_318 = lean_box(0);
}
x_319 = 1;
x_320 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
lean_dec(x_280);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_321 = lean_box(0);
if (lean_is_scalar(x_318)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_318;
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_317);
return x_322;
}
else
{
lean_object* x_323; 
lean_dec(x_318);
x_323 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_2, x_4, x_5, x_6, x_7, x_280, x_9, x_317);
return x_323;
}
}
else
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_314, 1);
lean_inc(x_324);
lean_dec(x_314);
x_325 = lean_box(0);
x_3 = x_325;
x_8 = x_280;
x_10 = x_324;
goto _start;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_280);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_327 = lean_ctor_get(x_314, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_314, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_329 = x_314;
} else {
 lean_dec_ref(x_314);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_310, 1);
lean_inc(x_331);
lean_dec(x_310);
x_332 = lean_box(0);
x_3 = x_332;
x_8 = x_280;
x_10 = x_331;
goto _start;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_280);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_334 = lean_ctor_get(x_310, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_310, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_336 = x_310;
} else {
 lean_dec_ref(x_310);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_335);
return x_337;
}
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_290);
x_338 = lean_ctor_get(x_306, 1);
lean_inc(x_338);
lean_dec(x_306);
x_339 = lean_box(0);
x_3 = x_339;
x_8 = x_280;
x_10 = x_338;
goto _start;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_290);
lean_dec(x_280);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_341 = lean_ctor_get(x_306, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_306, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_343 = x_306;
} else {
 lean_dec_ref(x_306);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_290);
x_345 = lean_ctor_get(x_302, 1);
lean_inc(x_345);
lean_dec(x_302);
x_346 = lean_box(0);
x_3 = x_346;
x_8 = x_280;
x_10 = x_345;
goto _start;
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_290);
lean_dec(x_280);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_348 = lean_ctor_get(x_302, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_302, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_350 = x_302;
} else {
 lean_dec_ref(x_302);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
else
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_290);
lean_dec(x_280);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_352 = lean_box(0);
if (lean_is_scalar(x_295)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_295;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_294);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_290);
x_354 = lean_ctor_get(x_291, 1);
lean_inc(x_354);
lean_dec(x_291);
x_355 = lean_box(0);
x_3 = x_355;
x_8 = x_280;
x_10 = x_354;
goto _start;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_290);
lean_dec(x_280);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_357 = lean_ctor_get(x_291, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_291, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_359 = x_291;
} else {
 lean_dec_ref(x_291);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_280);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_361 = lean_box(0);
if (lean_is_scalar(x_284)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_284;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_283);
return x_362;
}
}
else
{
lean_object* x_363; 
lean_dec(x_273);
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_261);
x_363 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1(x_275, x_4, x_5, x_6, x_7, x_276, x_9, x_13);
lean_dec(x_9);
lean_dec(x_276);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_363;
}
}
}
else
{
uint8_t x_364; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_364 = !lean_is_exclusive(x_11);
if (x_364 == 0)
{
return x_11;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_11, 0);
x_366 = lean_ctor_get(x_11, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_11);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
return x_367;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not ready yet", 13, 13);
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succeeded", 9, 9);
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__5;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1(x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_16;
}
else
{
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__3;
x_19 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1(x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__6;
x_25 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_1, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1(x_2, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_26);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("postpone", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
x_2 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resuming ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_22; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_15 = x_3;
} else {
 lean_dec_ref(x_3);
 x_15 = lean_box(0);
}
lean_inc(x_13);
x_49 = l_Lean_Expr_mvar___override(x_13);
x_50 = l_Lean_MessageData_ofExpr(x_49);
x_51 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_closure((void*)(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__3___boxed), 8, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2;
x_57 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_55);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_22 = x_60;
goto block_48;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_62 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_13, x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_56, x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_64);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_22 = x_66;
goto block_48;
}
else
{
uint8_t x_67; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
block_21:
{
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_13);
x_3 = x_14;
x_11 = x_17;
goto _start;
}
else
{
lean_object* x_19; 
if (lean_is_scalar(x_15)) {
 x_19 = lean_alloc_ctor(1, 2, 0);
} else {
 x_19 = x_15;
}
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_4);
x_3 = x_14;
x_4 = x_19;
x_11 = x_17;
goto _start;
}
}
block_48:
{
lean_object* x_23; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_23 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(x_13, x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2;
x_28 = lean_box(0);
x_29 = lean_unbox(x_24);
lean_dec(x_24);
x_30 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2(x_27, x_29, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unbox(x_31);
lean_dec(x_31);
x_16 = x_33;
x_17 = x_32;
goto block_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2;
x_39 = lean_unbox(x_24);
lean_dec(x_24);
x_40 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2(x_38, x_39, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
lean_dec(x_36);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unbox(x_41);
lean_dec(x_41);
x_16 = x_43;
x_17 = x_42;
goto block_21;
}
}
else
{
uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resuming synthetic metavariables, mayPostpone: ", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", postponeOnError: ", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__2;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__8;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__9;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__10;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__13;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__9;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__14;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__15;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__2;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__14;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__17;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__18;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__7;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__19;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__18;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__14;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__21;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_4 == 0)
{
if (x_2 == 0)
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__11;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__16;
return x_6;
}
}
else
{
if (x_2 == 0)
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__20;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__22;
return x_8;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resuming", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = lean_box(x_1);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_10);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2;
lean_inc(x_7);
x_13 = l_Lean_Elab_Term_traceAtCmdPos(x_12, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_4, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_List_lengthTRAux___rarg(x_18, x_19);
x_21 = lean_st_ref_take(x_4, x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_22, 2);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 2, x_26);
x_27 = lean_st_ref_set(x_4, x_22, x_23);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_List_reverse___rarg(x_18);
lean_inc(x_4);
x_30 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(x_1, x_2, x_29, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_take(x_4, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_34, 2);
lean_inc(x_31);
x_38 = l_List_appendTR___rarg(x_37, x_31);
lean_ctor_set(x_34, 2, x_38);
x_39 = lean_st_ref_set(x_4, x_34, x_35);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_List_lengthTRAux___rarg(x_31, x_19);
lean_dec(x_31);
x_43 = lean_nat_dec_eq(x_20, x_42);
lean_dec(x_42);
lean_dec(x_20);
if (x_43 == 0)
{
uint8_t x_44; lean_object* x_45; 
x_44 = 1;
x_45 = lean_box(x_44);
lean_ctor_set(x_39, 0, x_45);
return x_39;
}
else
{
uint8_t x_46; lean_object* x_47; 
x_46 = 0;
x_47 = lean_box(x_46);
lean_ctor_set(x_39, 0, x_47);
return x_39;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = l_List_lengthTRAux___rarg(x_31, x_19);
lean_dec(x_31);
x_50 = lean_nat_dec_eq(x_20, x_49);
lean_dec(x_49);
lean_dec(x_20);
if (x_50 == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_51 = 1;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_54 = 0;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_48);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_57 = lean_ctor_get(x_34, 0);
x_58 = lean_ctor_get(x_34, 1);
x_59 = lean_ctor_get(x_34, 2);
x_60 = lean_ctor_get(x_34, 3);
x_61 = lean_ctor_get(x_34, 4);
x_62 = lean_ctor_get(x_34, 5);
x_63 = lean_ctor_get(x_34, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_34);
lean_inc(x_31);
x_64 = l_List_appendTR___rarg(x_59, x_31);
x_65 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_58);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_60);
lean_ctor_set(x_65, 4, x_61);
lean_ctor_set(x_65, 5, x_62);
lean_ctor_set(x_65, 6, x_63);
x_66 = lean_st_ref_set(x_4, x_65, x_35);
lean_dec(x_4);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = l_List_lengthTRAux___rarg(x_31, x_19);
lean_dec(x_31);
x_70 = lean_nat_dec_eq(x_20, x_69);
lean_dec(x_69);
lean_dec(x_20);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_71 = 1;
x_72 = lean_box(x_71);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
return x_73;
}
else
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_74 = 0;
x_75 = lean_box(x_74);
if (lean_is_scalar(x_68)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_68;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_67);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_20);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_30);
if (x_77 == 0)
{
return x_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_30, 0);
x_79 = lean_ctor_get(x_30, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_30);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_81 = lean_ctor_get(x_22, 0);
x_82 = lean_ctor_get(x_22, 1);
x_83 = lean_ctor_get(x_22, 3);
x_84 = lean_ctor_get(x_22, 4);
x_85 = lean_ctor_get(x_22, 5);
x_86 = lean_ctor_get(x_22, 6);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_22);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_88, 0, x_81);
lean_ctor_set(x_88, 1, x_82);
lean_ctor_set(x_88, 2, x_87);
lean_ctor_set(x_88, 3, x_83);
lean_ctor_set(x_88, 4, x_84);
lean_ctor_set(x_88, 5, x_85);
lean_ctor_set(x_88, 6, x_86);
x_89 = lean_st_ref_set(x_4, x_88, x_23);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_List_reverse___rarg(x_18);
lean_inc(x_4);
x_92 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(x_1, x_2, x_91, x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_st_ref_take(x_4, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_96, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_96, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 lean_ctor_release(x_96, 5);
 lean_ctor_release(x_96, 6);
 x_105 = x_96;
} else {
 lean_dec_ref(x_96);
 x_105 = lean_box(0);
}
lean_inc(x_93);
x_106 = l_List_appendTR___rarg(x_100, x_93);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 7, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_98);
lean_ctor_set(x_107, 1, x_99);
lean_ctor_set(x_107, 2, x_106);
lean_ctor_set(x_107, 3, x_101);
lean_ctor_set(x_107, 4, x_102);
lean_ctor_set(x_107, 5, x_103);
lean_ctor_set(x_107, 6, x_104);
x_108 = lean_st_ref_set(x_4, x_107, x_97);
lean_dec(x_4);
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
x_111 = l_List_lengthTRAux___rarg(x_93, x_19);
lean_dec(x_93);
x_112 = lean_nat_dec_eq(x_20, x_111);
lean_dec(x_111);
lean_dec(x_20);
if (x_112 == 0)
{
uint8_t x_113; lean_object* x_114; lean_object* x_115; 
x_113 = 1;
x_114 = lean_box(x_113);
if (lean_is_scalar(x_110)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_110;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_109);
return x_115;
}
else
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_116 = 0;
x_117 = lean_box(x_116);
if (lean_is_scalar(x_110)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_110;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_109);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_20);
lean_dec(x_4);
x_119 = lean_ctor_get(x_92, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_92, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_121 = x_92;
} else {
 lean_dec_ref(x_92);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_coerce_x3f(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_15);
x_16 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_12, 0);
lean_dec(x_38);
x_39 = 0;
x_40 = lean_box(x_39);
lean_ctor_set(x_12, 0, x_40);
return x_12;
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_dec(x_12);
x_42 = 0;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_12);
if (x_45 == 0)
{
return x_12;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_12, 0);
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_12);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
static uint64_t _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint64_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 4);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 6);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_23 = 1;
lean_ctor_set_uint8(x_11, 9, x_23);
x_24 = 2;
x_25 = lean_uint64_shift_right(x_12, x_24);
x_26 = lean_uint64_shift_left(x_25, x_24);
x_27 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2___closed__1;
x_28 = lean_uint64_lor(x_26, x_27);
x_29 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_29, 2, x_15);
lean_ctor_set(x_29, 3, x_16);
lean_ctor_set(x_29, 4, x_17);
lean_ctor_set(x_29, 5, x_18);
lean_ctor_set(x_29, 6, x_19);
lean_ctor_set_uint64(x_29, sizeof(void*)*7, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 8, x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 9, x_21);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 10, x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_29);
lean_inc(x_1);
x_30 = lean_infer_type(x_1, x_29, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_33 = l_Lean_Meta_isExprDefEq(x_31, x_2, x_29, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(x_1, x_2, x_3, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
lean_inc(x_1);
x_40 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_box(0);
x_45 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(x_1, x_2, x_3, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_2);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = 1;
x_51 = lean_box(x_50);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_dec(x_47);
x_53 = 1;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_33);
if (x_56 == 0)
{
return x_33;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_33, 0);
x_58 = lean_ctor_get(x_33, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_33);
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
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_30);
if (x_60 == 0)
{
return x_30;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_30, 0);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_30);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_65 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_66 = lean_ctor_get_uint8(x_11, 0);
x_67 = lean_ctor_get_uint8(x_11, 1);
x_68 = lean_ctor_get_uint8(x_11, 2);
x_69 = lean_ctor_get_uint8(x_11, 3);
x_70 = lean_ctor_get_uint8(x_11, 4);
x_71 = lean_ctor_get_uint8(x_11, 5);
x_72 = lean_ctor_get_uint8(x_11, 6);
x_73 = lean_ctor_get_uint8(x_11, 7);
x_74 = lean_ctor_get_uint8(x_11, 8);
x_75 = lean_ctor_get_uint8(x_11, 10);
x_76 = lean_ctor_get_uint8(x_11, 11);
x_77 = lean_ctor_get_uint8(x_11, 12);
x_78 = lean_ctor_get_uint8(x_11, 13);
x_79 = lean_ctor_get_uint8(x_11, 14);
x_80 = lean_ctor_get_uint8(x_11, 15);
x_81 = lean_ctor_get_uint8(x_11, 16);
x_82 = lean_ctor_get_uint8(x_11, 17);
lean_dec(x_11);
x_83 = 1;
x_84 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_84, 0, x_66);
lean_ctor_set_uint8(x_84, 1, x_67);
lean_ctor_set_uint8(x_84, 2, x_68);
lean_ctor_set_uint8(x_84, 3, x_69);
lean_ctor_set_uint8(x_84, 4, x_70);
lean_ctor_set_uint8(x_84, 5, x_71);
lean_ctor_set_uint8(x_84, 6, x_72);
lean_ctor_set_uint8(x_84, 7, x_73);
lean_ctor_set_uint8(x_84, 8, x_74);
lean_ctor_set_uint8(x_84, 9, x_83);
lean_ctor_set_uint8(x_84, 10, x_75);
lean_ctor_set_uint8(x_84, 11, x_76);
lean_ctor_set_uint8(x_84, 12, x_77);
lean_ctor_set_uint8(x_84, 13, x_78);
lean_ctor_set_uint8(x_84, 14, x_79);
lean_ctor_set_uint8(x_84, 15, x_80);
lean_ctor_set_uint8(x_84, 16, x_81);
lean_ctor_set_uint8(x_84, 17, x_82);
x_85 = 2;
x_86 = lean_uint64_shift_right(x_12, x_85);
x_87 = lean_uint64_shift_left(x_86, x_85);
x_88 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2___closed__1;
x_89 = lean_uint64_lor(x_87, x_88);
x_90 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_14);
lean_ctor_set(x_90, 2, x_15);
lean_ctor_set(x_90, 3, x_16);
lean_ctor_set(x_90, 4, x_17);
lean_ctor_set(x_90, 5, x_18);
lean_ctor_set(x_90, 6, x_19);
lean_ctor_set_uint64(x_90, sizeof(void*)*7, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 8, x_13);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 9, x_64);
lean_ctor_set_uint8(x_90, sizeof(void*)*7 + 10, x_65);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_90);
lean_inc(x_1);
x_91 = lean_infer_type(x_1, x_90, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_94 = l_Lean_Meta_isExprDefEq(x_92, x_2, x_90, x_7, x_8, x_9, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_box(0);
x_99 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(x_1, x_2, x_3, x_98, x_4, x_5, x_6, x_7, x_8, x_9, x_97);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_dec(x_94);
lean_inc(x_1);
x_101 = l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_box(0);
x_106 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(x_1, x_2, x_3, x_105, x_4, x_5, x_6, x_7, x_8, x_9, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_2);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_dec(x_101);
x_108 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_107);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
x_111 = 1;
x_112 = lean_box(x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_109);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_ctor_get(x_94, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_94, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_116 = x_94;
} else {
 lean_dec_ref(x_94);
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
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_90);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = lean_ctor_get(x_91, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_91, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_120 = x_91;
} else {
 lean_dec_ref(x_91);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l_Lean_Elab_Term_runTactic(x_1, x_2, x_3, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(x_11);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(x_11);
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
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_ReaderT_pure___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__17___rarg___boxed), 8, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_8, 5);
x_27 = l_Lean_replaceRef(x_23, x_26);
lean_dec(x_26);
lean_ctor_set(x_8, 5, x_27);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_29;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 2);
lean_inc(x_31);
lean_dec(x_24);
lean_inc(x_1);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2___boxed), 10, 3);
lean_closure_set(x_32, 0, x_31);
lean_closure_set(x_32, 1, x_30);
lean_closure_set(x_32, 2, x_1);
x_33 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_33;
}
case 2:
{
lean_dec(x_23);
if (x_3 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1;
x_36 = l_Lean_Elab_Term_withSavedContext___rarg(x_34, x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_24, 2);
lean_inc(x_39);
lean_dec(x_24);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__3), 10, 3);
lean_closure_set(x_40, 0, x_1);
lean_closure_set(x_40, 1, x_37);
lean_closure_set(x_40, 2, x_39);
x_41 = l_Lean_Elab_Term_withSavedContext___rarg(x_38, x_40, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_41;
}
}
default: 
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_24, 0);
lean_inc(x_42);
lean_dec(x_24);
x_43 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(x_42, x_23, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_8, 1);
x_46 = lean_ctor_get(x_8, 2);
x_47 = lean_ctor_get(x_8, 3);
x_48 = lean_ctor_get(x_8, 4);
x_49 = lean_ctor_get(x_8, 5);
x_50 = lean_ctor_get(x_8, 6);
x_51 = lean_ctor_get(x_8, 7);
x_52 = lean_ctor_get(x_8, 8);
x_53 = lean_ctor_get(x_8, 9);
x_54 = lean_ctor_get(x_8, 10);
x_55 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_56 = lean_ctor_get(x_8, 11);
x_57 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_56);
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
lean_dec(x_8);
x_58 = l_Lean_replaceRef(x_23, x_49);
lean_dec(x_49);
x_59 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_59, 0, x_44);
lean_ctor_set(x_59, 1, x_45);
lean_ctor_set(x_59, 2, x_46);
lean_ctor_set(x_59, 3, x_47);
lean_ctor_set(x_59, 4, x_48);
lean_ctor_set(x_59, 5, x_58);
lean_ctor_set(x_59, 6, x_50);
lean_ctor_set(x_59, 7, x_51);
lean_ctor_set(x_59, 8, x_52);
lean_ctor_set(x_59, 9, x_53);
lean_ctor_set(x_59, 10, x_54);
lean_ctor_set(x_59, 11, x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*12, x_55);
lean_ctor_set_uint8(x_59, sizeof(void*)*12 + 1, x_57);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_23);
x_60 = lean_ctor_get(x_24, 0);
lean_inc(x_60);
lean_dec(x_24);
x_61 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(x_1, x_60, x_4, x_5, x_6, x_7, x_59, x_9, x_21);
return x_61;
}
case 1:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_23);
x_62 = lean_ctor_get(x_24, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_24, 2);
lean_inc(x_63);
lean_dec(x_24);
lean_inc(x_1);
x_64 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2___boxed), 10, 3);
lean_closure_set(x_64, 0, x_63);
lean_closure_set(x_64, 1, x_62);
lean_closure_set(x_64, 2, x_1);
x_65 = l_Lean_MVarId_withContext___at_Lean_Elab_Tactic_run___spec__1___rarg(x_1, x_64, x_4, x_5, x_6, x_7, x_59, x_9, x_21);
return x_65;
}
case 2:
{
lean_dec(x_23);
if (x_3 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_1);
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
lean_dec(x_24);
x_67 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1;
x_68 = l_Lean_Elab_Term_withSavedContext___rarg(x_66, x_67, x_4, x_5, x_6, x_7, x_59, x_9, x_21);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_24, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_24, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_24, 2);
lean_inc(x_71);
lean_dec(x_24);
x_72 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__3), 10, 3);
lean_closure_set(x_72, 0, x_1);
lean_closure_set(x_72, 1, x_69);
lean_closure_set(x_72, 2, x_71);
x_73 = l_Lean_Elab_Term_withSavedContext___rarg(x_70, x_72, x_4, x_5, x_6, x_7, x_59, x_9, x_21);
return x_73;
}
}
default: 
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_24, 0);
lean_inc(x_74);
lean_dec(x_24);
x_75 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(x_74, x_23, x_1, x_2, x_4, x_5, x_6, x_7, x_59, x_9, x_21);
return x_75;
}
}
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_runTactic___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_instMonadTermElabM;
x_2 = l_Lean_instInhabitedLocalContext;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_runTactic___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Elab_Term_runTactic___spec__3___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__7(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid auxiliary declaration found in local context: ", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" does not have an associated full name.", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.instantiateLCtxMVars", 25, 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
x_15 = x_5;
x_16 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 1);
x_23 = lean_box(x_22);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(x_1, x_24);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_5);
x_31 = 1;
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1;
x_33 = l_Lean_Name_toString(x_25, x_31, x_32);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4;
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5;
x_40 = lean_unsigned_to_nat(597u);
x_41 = lean_unsigned_to_nat(12u);
x_42 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_37);
lean_dec(x_37);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_panic___at_Lean_Elab_Term_runTactic___spec__3(x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_15 = x_44;
x_16 = x_45;
goto block_20;
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_30, 0);
lean_inc(x_50);
lean_dec(x_30);
x_51 = l_Lean_LocalContext_mkAuxDecl(x_5, x_24, x_25, x_28, x_50);
x_15 = x_51;
x_16 = x_29;
goto block_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_23);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_21, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_21, 3);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
lean_dec(x_21);
x_56 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_LocalContext_mkLocalDecl(x_5, x_52, x_53, x_57, x_55, x_22);
x_15 = x_59;
x_16 = x_58;
goto block_20;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_21, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_21, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_21, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_21, 4);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_21, sizeof(void*)*5);
x_65 = lean_ctor_get_uint8(x_21, sizeof(void*)*5 + 1);
lean_dec(x_21);
x_66 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_63, x_6, x_7, x_8, x_9, x_10, x_11, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_LocalContext_mkLetDecl(x_5, x_60, x_61, x_67, x_70, x_64, x_65);
x_15 = x_72;
x_16 = x_71;
goto block_20;
}
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_12 = x_16;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_12, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(x_1, x_11, x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9(x_1, x_21, x_28, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__7(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
x_15 = x_5;
x_16 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 1);
x_23 = lean_box(x_22);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(x_1, x_24);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_5);
x_31 = 1;
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1;
x_33 = l_Lean_Name_toString(x_25, x_31, x_32);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4;
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5;
x_40 = lean_unsigned_to_nat(597u);
x_41 = lean_unsigned_to_nat(12u);
x_42 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_37);
lean_dec(x_37);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_panic___at_Lean_Elab_Term_runTactic___spec__3(x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_15 = x_44;
x_16 = x_45;
goto block_20;
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_30, 0);
lean_inc(x_50);
lean_dec(x_30);
x_51 = l_Lean_LocalContext_mkAuxDecl(x_5, x_24, x_25, x_28, x_50);
x_15 = x_51;
x_16 = x_29;
goto block_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_23);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_21, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_21, 3);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
lean_dec(x_21);
x_56 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_LocalContext_mkLocalDecl(x_5, x_52, x_53, x_57, x_55, x_22);
x_15 = x_59;
x_16 = x_58;
goto block_20;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_21, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_21, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_21, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_21, 4);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_21, sizeof(void*)*5);
x_65 = lean_ctor_get_uint8(x_21, sizeof(void*)*5 + 1);
lean_dec(x_21);
x_66 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_63, x_6, x_7, x_8, x_9, x_10, x_11, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_LocalContext_mkLetDecl(x_5, x_60, x_61, x_67, x_70, x_64, x_65);
x_15 = x_72;
x_16 = x_71;
goto block_20;
}
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_12 = x_16;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_usize_shift_right(x_3, x_4);
x_15 = lean_usize_to_nat(x_14);
x_16 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6___closed__1;
x_17 = lean_array_get(x_16, x_13, x_15);
x_18 = 1;
x_19 = lean_usize_shift_left(x_18, x_4);
x_20 = lean_usize_sub(x_19, x_18);
x_21 = lean_usize_land(x_3, x_20);
x_22 = 5;
x_23 = lean_usize_sub(x_4, x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6(x_1, x_17, x_21, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_17);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_15, x_28);
lean_dec(x_15);
x_30 = lean_array_get_size(x_13);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
lean_free_object(x_24);
x_33 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__10(x_1, x_13, x_33, x_34, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_15, x_38);
lean_dec(x_15);
x_40 = lean_array_get_size(x_13);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_40, x_40);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_46 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_47 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__10(x_1, x_13, x_45, x_46, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_24);
if (x_48 == 0)
{
return x_24;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_24, 0);
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_24);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_2, 0);
x_53 = lean_usize_to_nat(x_3);
x_54 = lean_array_get_size(x_52);
x_55 = lean_nat_dec_lt(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_5);
lean_ctor_set(x_56, 1, x_12);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_54, x_54);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_5);
lean_ctor_set(x_58, 1, x_12);
return x_58;
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; 
x_59 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_60 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_61 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__11(x_1, x_52, x_59, x_60, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
x_15 = x_5;
x_16 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 1);
x_23 = lean_box(x_22);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(x_1, x_24);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_5);
x_31 = 1;
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1;
x_33 = l_Lean_Name_toString(x_25, x_31, x_32);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4;
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5;
x_40 = lean_unsigned_to_nat(597u);
x_41 = lean_unsigned_to_nat(12u);
x_42 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_37);
lean_dec(x_37);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_panic___at_Lean_Elab_Term_runTactic___spec__3(x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_15 = x_44;
x_16 = x_45;
goto block_20;
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_30, 0);
lean_inc(x_50);
lean_dec(x_30);
x_51 = l_Lean_LocalContext_mkAuxDecl(x_5, x_24, x_25, x_28, x_50);
x_15 = x_51;
x_16 = x_29;
goto block_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_23);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_21, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_21, 3);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
lean_dec(x_21);
x_56 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_LocalContext_mkLocalDecl(x_5, x_52, x_53, x_57, x_55, x_22);
x_15 = x_59;
x_16 = x_58;
goto block_20;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_21, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_21, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_21, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_21, 4);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_21, sizeof(void*)*5);
x_65 = lean_ctor_get_uint8(x_21, sizeof(void*)*5 + 1);
lean_dec(x_21);
x_66 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_63, x_6, x_7, x_8, x_9, x_10, x_11, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_LocalContext_mkLetDecl(x_5, x_60, x_61, x_67, x_70, x_64, x_65);
x_15 = x_72;
x_16 = x_71;
goto block_20;
}
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_12 = x_16;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
x_15 = x_5;
x_16 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 1);
x_23 = lean_box(x_22);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(x_1, x_24);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_5);
x_31 = 1;
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1;
x_33 = l_Lean_Name_toString(x_25, x_31, x_32);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4;
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5;
x_40 = lean_unsigned_to_nat(597u);
x_41 = lean_unsigned_to_nat(12u);
x_42 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_37);
lean_dec(x_37);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_panic___at_Lean_Elab_Term_runTactic___spec__3(x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_15 = x_44;
x_16 = x_45;
goto block_20;
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_30, 0);
lean_inc(x_50);
lean_dec(x_30);
x_51 = l_Lean_LocalContext_mkAuxDecl(x_5, x_24, x_25, x_28, x_50);
x_15 = x_51;
x_16 = x_29;
goto block_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_23);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_21, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_21, 3);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
lean_dec(x_21);
x_56 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_LocalContext_mkLocalDecl(x_5, x_52, x_53, x_57, x_55, x_22);
x_15 = x_59;
x_16 = x_58;
goto block_20;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_21, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_21, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_21, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_21, 4);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_21, sizeof(void*)*5);
x_65 = lean_ctor_get_uint8(x_21, sizeof(void*)*5 + 1);
lean_dec(x_21);
x_66 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_63, x_6, x_7, x_8, x_9, x_10, x_11, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_LocalContext_mkLetDecl(x_5, x_60, x_61, x_67, x_70, x_64, x_65);
x_15 = x_72;
x_16 = x_71;
goto block_20;
}
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_12 = x_16;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__15(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__14(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__16(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
x_15 = x_5;
x_16 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 1);
x_23 = lean_box(x_22);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(x_1, x_24);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_5);
x_31 = 1;
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1;
x_33 = l_Lean_Name_toString(x_25, x_31, x_32);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4;
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5;
x_40 = lean_unsigned_to_nat(597u);
x_41 = lean_unsigned_to_nat(12u);
x_42 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_37);
lean_dec(x_37);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_panic___at_Lean_Elab_Term_runTactic___spec__3(x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_15 = x_44;
x_16 = x_45;
goto block_20;
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_30, 0);
lean_inc(x_50);
lean_dec(x_30);
x_51 = l_Lean_LocalContext_mkAuxDecl(x_5, x_24, x_25, x_28, x_50);
x_15 = x_51;
x_16 = x_29;
goto block_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_23);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_21, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_21, 3);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
lean_dec(x_21);
x_56 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_LocalContext_mkLocalDecl(x_5, x_52, x_53, x_57, x_55, x_22);
x_15 = x_59;
x_16 = x_58;
goto block_20;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_21, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_21, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_21, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_21, 4);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_21, sizeof(void*)*5);
x_65 = lean_ctor_get_uint8(x_21, sizeof(void*)*5 + 1);
lean_dec(x_21);
x_66 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_63, x_6, x_7, x_8, x_9, x_10, x_11, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_LocalContext_mkLetDecl(x_5, x_60, x_61, x_67, x_70, x_64, x_65);
x_15 = x_72;
x_16 = x_71;
goto block_20;
}
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_12 = x_16;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_12, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__15(x_1, x_11, x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__16(x_1, x_21, x_28, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__17(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
x_15 = x_5;
x_16 = x_12;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 1);
x_23 = lean_box(x_22);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(x_1, x_24);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_5);
x_31 = 1;
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1;
x_33 = l_Lean_Name_toString(x_25, x_31, x_32);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4;
x_39 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5;
x_40 = lean_unsigned_to_nat(597u);
x_41 = lean_unsigned_to_nat(12u);
x_42 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_37);
lean_dec(x_37);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_43 = l_panic___at_Lean_Elab_Term_runTactic___spec__3(x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_15 = x_44;
x_16 = x_45;
goto block_20;
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_30, 0);
lean_inc(x_50);
lean_dec(x_30);
x_51 = l_Lean_LocalContext_mkAuxDecl(x_5, x_24, x_25, x_28, x_50);
x_15 = x_51;
x_16 = x_29;
goto block_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_23);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_21, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_21, 3);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_21, sizeof(void*)*4);
lean_dec(x_21);
x_56 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_LocalContext_mkLocalDecl(x_5, x_52, x_53, x_57, x_55, x_22);
x_15 = x_59;
x_16 = x_58;
goto block_20;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_21, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_21, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_21, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_21, 4);
lean_inc(x_63);
x_64 = lean_ctor_get_uint8(x_21, sizeof(void*)*5);
x_65 = lean_ctor_get_uint8(x_21, sizeof(void*)*5 + 1);
lean_dec(x_21);
x_66 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_63, x_6, x_7, x_8, x_9, x_10, x_11, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_LocalContext_mkLetDecl(x_5, x_60, x_61, x_67, x_70, x_64, x_65);
x_15 = x_72;
x_16 = x_71;
goto block_20;
}
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_15;
x_12 = x_16;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_Elab_Term_runTactic___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_nat_dec_le(x_14, x_4);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_usize_of_nat(x_4);
x_18 = lean_ctor_get_usize(x_2, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6(x_1, x_16, x_17, x_18, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_array_get_size(x_23);
x_25 = lean_nat_dec_lt(x_12, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
lean_free_object(x_19);
x_27 = 0;
x_28 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__12(x_1, x_23, x_27, x_28, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_array_get_size(x_32);
x_34 = lean_nat_dec_lt(x_12, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_33, x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__12(x_1, x_32, x_38, x_39, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_nat_sub(x_4, x_14);
x_47 = lean_array_get_size(x_45);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_11);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_47, x_47);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_11);
return x_51;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_53 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_54 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__13(x_1, x_45, x_52, x_53, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_56 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__14(x_1, x_55, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
x_60 = lean_ctor_get(x_2, 1);
x_61 = lean_array_get_size(x_60);
x_62 = lean_nat_dec_lt(x_12, x_61);
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_56;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_61, x_61);
if (x_63 == 0)
{
lean_dec(x_61);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_56;
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; 
lean_free_object(x_56);
x_64 = 0;
x_65 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_66 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__17(x_1, x_60, x_64, x_65, x_58, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_56, 0);
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_56);
x_69 = lean_ctor_get(x_2, 1);
x_70 = lean_array_get_size(x_69);
x_71 = lean_nat_dec_lt(x_12, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_70);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_70, x_70);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_70);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_77 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__17(x_1, x_69, x_75, x_76, x_67, x_5, x_6, x_7, x_8, x_9, x_10, x_68);
return x_77;
}
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
x_78 = !lean_is_exclusive(x_56);
if (x_78 == 0)
{
return x_56;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_56, 0);
x_80 = lean_ctor_get(x_56, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_56);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Term_runTactic___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_Lean_PersistentArray_foldlM___at_Lean_Elab_Term_runTactic___spec__5(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__4;
x_3 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__3;
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
static lean_object* _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__2;
x_3 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__6;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_LocalContext_foldlM___at_Lean_Elab_Term_runTactic___spec__4(x_9, x_1, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVarDeclMVars___at_Lean_Elab_Term_runTactic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_MetavarContext_getDecl(x_12, x_1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 4);
x_20 = lean_ctor_get(x_13, 5);
x_21 = lean_ctor_get(x_13, 6);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_ctor_set(x_25, 1, x_27);
lean_ctor_set(x_25, 0, x_23);
x_29 = lean_sharecommon_quick(x_25);
lean_dec(x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_take(x_5, x_28);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_34, 4);
lean_ctor_set(x_13, 2, x_31);
lean_ctor_set(x_13, 1, x_30);
x_40 = l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(x_39, x_1, x_13);
lean_ctor_set(x_34, 4, x_40);
x_41 = lean_st_ref_set(x_5, x_33, x_35);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
x_50 = lean_ctor_get(x_34, 2);
x_51 = lean_ctor_get(x_34, 3);
x_52 = lean_ctor_get(x_34, 4);
x_53 = lean_ctor_get(x_34, 5);
x_54 = lean_ctor_get(x_34, 6);
x_55 = lean_ctor_get(x_34, 7);
x_56 = lean_ctor_get(x_34, 8);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
lean_ctor_set(x_13, 2, x_31);
lean_ctor_set(x_13, 1, x_30);
x_57 = l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(x_52, x_1, x_13);
x_58 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set(x_58, 2, x_50);
lean_ctor_set(x_58, 3, x_51);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set(x_58, 5, x_53);
lean_ctor_set(x_58, 6, x_54);
lean_ctor_set(x_58, 7, x_55);
lean_ctor_set(x_58, 8, x_56);
lean_ctor_set(x_33, 0, x_58);
x_59 = lean_st_ref_set(x_5, x_33, x_35);
lean_dec(x_5);
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
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_64 = lean_ctor_get(x_33, 1);
x_65 = lean_ctor_get(x_33, 2);
x_66 = lean_ctor_get(x_33, 3);
x_67 = lean_ctor_get(x_33, 4);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_33);
x_68 = lean_ctor_get(x_34, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_34, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_34, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_34, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_34, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_34, 6);
lean_inc(x_74);
x_75 = lean_ctor_get(x_34, 7);
lean_inc(x_75);
x_76 = lean_ctor_get(x_34, 8);
lean_inc(x_76);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 lean_ctor_release(x_34, 4);
 lean_ctor_release(x_34, 5);
 lean_ctor_release(x_34, 6);
 lean_ctor_release(x_34, 7);
 lean_ctor_release(x_34, 8);
 x_77 = x_34;
} else {
 lean_dec_ref(x_34);
 x_77 = lean_box(0);
}
lean_ctor_set(x_13, 2, x_31);
lean_ctor_set(x_13, 1, x_30);
x_78 = l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(x_72, x_1, x_13);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 9, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_69);
lean_ctor_set(x_79, 2, x_70);
lean_ctor_set(x_79, 3, x_71);
lean_ctor_set(x_79, 4, x_78);
lean_ctor_set(x_79, 5, x_73);
lean_ctor_set(x_79, 6, x_74);
lean_ctor_set(x_79, 7, x_75);
lean_ctor_set(x_79, 8, x_76);
x_80 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_64);
lean_ctor_set(x_80, 2, x_65);
lean_ctor_set(x_80, 3, x_66);
lean_ctor_set(x_80, 4, x_67);
x_81 = lean_st_ref_set(x_5, x_80, x_35);
lean_dec(x_5);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_86 = lean_ctor_get(x_25, 0);
x_87 = lean_ctor_get(x_25, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_25);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_23);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_sharecommon_quick(x_88);
lean_dec(x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_take(x_5, x_87);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_93, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 4);
lean_inc(x_99);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 lean_ctor_release(x_93, 4);
 x_100 = x_93;
} else {
 lean_dec_ref(x_93);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_94, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_94, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_94, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_94, 5);
lean_inc(x_106);
x_107 = lean_ctor_get(x_94, 6);
lean_inc(x_107);
x_108 = lean_ctor_get(x_94, 7);
lean_inc(x_108);
x_109 = lean_ctor_get(x_94, 8);
lean_inc(x_109);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 lean_ctor_release(x_94, 3);
 lean_ctor_release(x_94, 4);
 lean_ctor_release(x_94, 5);
 lean_ctor_release(x_94, 6);
 lean_ctor_release(x_94, 7);
 lean_ctor_release(x_94, 8);
 x_110 = x_94;
} else {
 lean_dec_ref(x_94);
 x_110 = lean_box(0);
}
lean_ctor_set(x_13, 2, x_91);
lean_ctor_set(x_13, 1, x_90);
x_111 = l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(x_105, x_1, x_13);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 9, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_101);
lean_ctor_set(x_112, 1, x_102);
lean_ctor_set(x_112, 2, x_103);
lean_ctor_set(x_112, 3, x_104);
lean_ctor_set(x_112, 4, x_111);
lean_ctor_set(x_112, 5, x_106);
lean_ctor_set(x_112, 6, x_107);
lean_ctor_set(x_112, 7, x_108);
lean_ctor_set(x_112, 8, x_109);
if (lean_is_scalar(x_100)) {
 x_113 = lean_alloc_ctor(0, 5, 0);
} else {
 x_113 = x_100;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_96);
lean_ctor_set(x_113, 2, x_97);
lean_ctor_set(x_113, 3, x_98);
lean_ctor_set(x_113, 4, x_99);
x_114 = lean_st_ref_set(x_5, x_113, x_95);
lean_dec(x_5);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = lean_box(0);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
}
else
{
uint8_t x_119; 
lean_free_object(x_13);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_22);
if (x_119 == 0)
{
return x_22;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_22, 0);
x_121 = lean_ctor_get(x_22, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_22);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_123 = lean_ctor_get(x_13, 0);
x_124 = lean_ctor_get(x_13, 1);
x_125 = lean_ctor_get(x_13, 2);
x_126 = lean_ctor_get(x_13, 3);
x_127 = lean_ctor_get(x_13, 4);
x_128 = lean_ctor_get_uint8(x_13, sizeof(void*)*7);
x_129 = lean_ctor_get(x_13, 5);
x_130 = lean_ctor_get(x_13, 6);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_131 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2(x_124, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_124);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_125, x_2, x_3, x_4, x_5, x_6, x_7, x_133);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_135);
x_139 = lean_sharecommon_quick(x_138);
lean_dec(x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_st_ref_take(x_5, x_136);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_143, 4);
lean_inc(x_149);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 lean_ctor_release(x_143, 2);
 lean_ctor_release(x_143, 3);
 lean_ctor_release(x_143, 4);
 x_150 = x_143;
} else {
 lean_dec_ref(x_143);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_144, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_144, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_144, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_144, 3);
lean_inc(x_154);
x_155 = lean_ctor_get(x_144, 4);
lean_inc(x_155);
x_156 = lean_ctor_get(x_144, 5);
lean_inc(x_156);
x_157 = lean_ctor_get(x_144, 6);
lean_inc(x_157);
x_158 = lean_ctor_get(x_144, 7);
lean_inc(x_158);
x_159 = lean_ctor_get(x_144, 8);
lean_inc(x_159);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 lean_ctor_release(x_144, 2);
 lean_ctor_release(x_144, 3);
 lean_ctor_release(x_144, 4);
 lean_ctor_release(x_144, 5);
 lean_ctor_release(x_144, 6);
 lean_ctor_release(x_144, 7);
 lean_ctor_release(x_144, 8);
 x_160 = x_144;
} else {
 lean_dec_ref(x_144);
 x_160 = lean_box(0);
}
x_161 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_161, 0, x_123);
lean_ctor_set(x_161, 1, x_140);
lean_ctor_set(x_161, 2, x_141);
lean_ctor_set(x_161, 3, x_126);
lean_ctor_set(x_161, 4, x_127);
lean_ctor_set(x_161, 5, x_129);
lean_ctor_set(x_161, 6, x_130);
lean_ctor_set_uint8(x_161, sizeof(void*)*7, x_128);
x_162 = l_Lean_PersistentHashMap_insert___at_Lean_instantiateMVarDeclMVars___spec__1(x_155, x_1, x_161);
if (lean_is_scalar(x_160)) {
 x_163 = lean_alloc_ctor(0, 9, 0);
} else {
 x_163 = x_160;
}
lean_ctor_set(x_163, 0, x_151);
lean_ctor_set(x_163, 1, x_152);
lean_ctor_set(x_163, 2, x_153);
lean_ctor_set(x_163, 3, x_154);
lean_ctor_set(x_163, 4, x_162);
lean_ctor_set(x_163, 5, x_156);
lean_ctor_set(x_163, 6, x_157);
lean_ctor_set(x_163, 7, x_158);
lean_ctor_set(x_163, 8, x_159);
if (lean_is_scalar(x_150)) {
 x_164 = lean_alloc_ctor(0, 5, 0);
} else {
 x_164 = x_150;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_146);
lean_ctor_set(x_164, 2, x_147);
lean_ctor_set(x_164, 3, x_148);
lean_ctor_set(x_164, 4, x_149);
x_165 = lean_st_ref_set(x_5, x_164, x_145);
lean_dec(x_5);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
x_168 = lean_box(0);
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_167;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_166);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_ctor_get(x_131, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_131, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_172 = x_131;
} else {
 lean_dec_ref(x_131);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withReuseContext___at_Lean_Elab_Term_runTactic___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_9, sizeof(void*)*12 + 1);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 5);
lean_dec(x_14);
x_15 = 0;
lean_ctor_set(x_9, 5, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*12 + 1, x_15);
x_16 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
x_19 = lean_ctor_get(x_9, 2);
x_20 = lean_ctor_get(x_9, 3);
x_21 = lean_ctor_get(x_9, 4);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
x_24 = lean_ctor_get(x_9, 8);
x_25 = lean_ctor_get(x_9, 9);
x_26 = lean_ctor_get(x_9, 10);
x_27 = lean_ctor_get_uint8(x_9, sizeof(void*)*12);
x_28 = lean_ctor_get(x_9, 11);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_29 = 0;
x_30 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set(x_30, 3, x_20);
lean_ctor_set(x_30, 4, x_21);
lean_ctor_set(x_30, 5, x_1);
lean_ctor_set(x_30, 6, x_22);
lean_ctor_set(x_30, 7, x_23);
lean_ctor_set(x_30, 8, x_24);
lean_ctor_set(x_30, 9, x_25);
lean_ctor_set(x_30, 10, x_26);
lean_ctor_set(x_30, 11, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*12, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*12 + 1, x_29);
x_31 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30, x_10, x_11);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 5);
lean_dec(x_33);
lean_inc(x_1);
x_34 = l_Lean_Syntax_hasMissing(x_1);
lean_ctor_set(x_9, 5, x_1);
lean_ctor_set_uint8(x_9, sizeof(void*)*12 + 1, x_34);
x_35 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_9, 0);
x_37 = lean_ctor_get(x_9, 1);
x_38 = lean_ctor_get(x_9, 2);
x_39 = lean_ctor_get(x_9, 3);
x_40 = lean_ctor_get(x_9, 4);
x_41 = lean_ctor_get(x_9, 6);
x_42 = lean_ctor_get(x_9, 7);
x_43 = lean_ctor_get(x_9, 8);
x_44 = lean_ctor_get(x_9, 9);
x_45 = lean_ctor_get(x_9, 10);
x_46 = lean_ctor_get_uint8(x_9, sizeof(void*)*12);
x_47 = lean_ctor_get(x_9, 11);
lean_inc(x_47);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_9);
lean_inc(x_1);
x_48 = l_Lean_Syntax_hasMissing(x_1);
x_49 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_49, 0, x_36);
lean_ctor_set(x_49, 1, x_37);
lean_ctor_set(x_49, 2, x_38);
lean_ctor_set(x_49, 3, x_39);
lean_ctor_set(x_49, 4, x_40);
lean_ctor_set(x_49, 5, x_1);
lean_ctor_set(x_49, 6, x_41);
lean_ctor_set(x_49, 7, x_42);
lean_ctor_set(x_49, 8, x_43);
lean_ctor_set(x_49, 9, x_44);
lean_ctor_set(x_49, 10, x_45);
lean_ctor_set(x_49, 11, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*12, x_46);
lean_ctor_set_uint8(x_49, sizeof(void*)*12 + 1, x_48);
x_50 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_49, x_10, x_11);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
x_13 = lean_apply_1(x_1, x_2);
x_14 = l_Lean_Elab_Term_withReuseContext___at_Lean_Elab_Term_runTactic___spec__20(x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_3);
x_14 = lean_ctor_get(x_6, 6);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_6, 6);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_6, 6, x_18);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_15, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_25 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_26 = lean_ctor_get(x_6, 2);
x_27 = lean_ctor_get(x_6, 3);
x_28 = lean_ctor_get(x_6, 4);
x_29 = lean_ctor_get(x_6, 5);
x_30 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
x_31 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 4);
x_32 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 5);
x_33 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 6);
x_34 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 7);
x_35 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_36 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_37 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_39, 0, x_21);
lean_ctor_set(x_39, 1, x_22);
lean_ctor_set(x_39, 2, x_26);
lean_ctor_set(x_39, 3, x_27);
lean_ctor_set(x_39, 4, x_28);
lean_ctor_set(x_39, 5, x_29);
lean_ctor_set(x_39, 6, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*7, x_23);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 1, x_24);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 2, x_25);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 3, x_30);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 4, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 5, x_32);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 6, x_33);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 7, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 8, x_35);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 9, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 10, x_37);
x_40 = lean_box(0);
x_41 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_15, x_40, x_4, x_5, x_39, x_7, x_8, x_9, x_10, x_11, x_12);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_1);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_dec(x_13);
x_46 = !lean_is_exclusive(x_6);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_6, 6);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_43, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_43, 0, x_50);
x_51 = lean_box(0);
x_52 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_45, x_51, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_14, 0, x_55);
x_56 = lean_box(0);
x_57 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_45, x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_6, 1);
x_60 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_61 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_62 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_63 = lean_ctor_get(x_6, 2);
x_64 = lean_ctor_get(x_6, 3);
x_65 = lean_ctor_get(x_6, 4);
x_66 = lean_ctor_get(x_6, 5);
x_67 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
x_68 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 4);
x_69 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 5);
x_70 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 6);
x_71 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 7);
x_72 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_73 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_74 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_6);
x_75 = lean_ctor_get(x_43, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_76 = x_43;
} else {
 lean_dec_ref(x_43);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_14, 0, x_78);
x_79 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_79, 0, x_58);
lean_ctor_set(x_79, 1, x_59);
lean_ctor_set(x_79, 2, x_63);
lean_ctor_set(x_79, 3, x_64);
lean_ctor_set(x_79, 4, x_65);
lean_ctor_set(x_79, 5, x_66);
lean_ctor_set(x_79, 6, x_14);
lean_ctor_set_uint8(x_79, sizeof(void*)*7, x_60);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 1, x_61);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 2, x_62);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 3, x_67);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 4, x_68);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 5, x_69);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 6, x_70);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 7, x_71);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 8, x_72);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 9, x_73);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 10, x_74);
x_80 = lean_box(0);
x_81 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_45, x_80, x_4, x_5, x_79, x_7, x_8, x_9, x_10, x_11, x_12);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_13, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_13, 1);
lean_inc(x_83);
lean_dec(x_13);
x_84 = lean_ctor_get(x_10, 2);
lean_inc(x_84);
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_6, 6);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_43);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_43, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_44);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_90 = lean_ctor_get(x_44, 0);
x_104 = lean_ctor_get(x_90, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_90, 1);
lean_inc(x_105);
x_106 = lean_apply_1(x_1, x_104);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_ctor_get(x_106, 1);
x_110 = l_Lean_Syntax_eqWithInfoAndTraceReuse(x_84, x_82, x_108);
lean_dec(x_84);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
lean_free_object(x_106);
lean_dec(x_109);
lean_dec(x_105);
lean_free_object(x_14);
x_112 = lean_box(0);
lean_ctor_set(x_43, 0, x_112);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_6, 6, x_44);
x_91 = x_6;
goto block_103;
}
else
{
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 0, x_109);
lean_ctor_set(x_44, 0, x_106);
x_91 = x_6;
goto block_103;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_106, 0);
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_106);
x_115 = l_Lean_Syntax_eqWithInfoAndTraceReuse(x_84, x_82, x_113);
lean_dec(x_84);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_114);
lean_dec(x_105);
lean_free_object(x_14);
x_117 = lean_box(0);
lean_ctor_set(x_43, 0, x_117);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_6, 6, x_44);
x_91 = x_6;
goto block_103;
}
else
{
lean_object* x_118; 
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_114);
lean_ctor_set(x_118, 1, x_105);
lean_ctor_set(x_44, 0, x_118);
x_91 = x_6;
goto block_103;
}
}
block_103:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 6);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec(x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_dec(x_90);
x_96 = l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot;
x_97 = l_Lean_Language_SnapshotTask_cancelRec___rarg(x_96, x_95, x_12);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_83, x_98, x_4, x_5, x_91, x_7, x_8, x_9, x_10, x_11, x_99);
lean_dec(x_98);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_94);
lean_dec(x_90);
x_101 = lean_box(0);
x_102 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_83, x_101, x_4, x_5, x_91, x_7, x_8, x_9, x_10, x_11, x_12);
return x_102;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_119 = lean_ctor_get(x_44, 0);
lean_inc(x_119);
lean_dec(x_44);
x_133 = lean_ctor_get(x_119, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_119, 1);
lean_inc(x_134);
x_135 = lean_apply_1(x_1, x_133);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = l_Lean_Syntax_eqWithInfoAndTraceReuse(x_84, x_82, x_136);
lean_dec(x_84);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_134);
lean_free_object(x_14);
x_141 = lean_box(0);
lean_ctor_set(x_43, 0, x_141);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_43);
lean_ctor_set(x_6, 6, x_142);
x_120 = x_6;
goto block_132;
}
else
{
lean_object* x_143; lean_object* x_144; 
if (lean_is_scalar(x_138)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_138;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_134);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_43, 0, x_144);
x_120 = x_6;
goto block_132;
}
block_132:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 6);
lean_inc(x_121);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec(x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot;
x_126 = l_Lean_Language_SnapshotTask_cancelRec___rarg(x_125, x_124, x_12);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_83, x_127, x_4, x_5, x_120, x_7, x_8, x_9, x_10, x_11, x_128);
lean_dec(x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_123);
lean_dec(x_119);
x_130 = lean_box(0);
x_131 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_83, x_130, x_4, x_5, x_120, x_7, x_8, x_9, x_10, x_11, x_12);
return x_131;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_145 = lean_ctor_get(x_43, 1);
lean_inc(x_145);
lean_dec(x_43);
x_146 = lean_ctor_get(x_44, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_147 = x_44;
} else {
 lean_dec_ref(x_44);
 x_147 = lean_box(0);
}
x_161 = lean_ctor_get(x_146, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_146, 1);
lean_inc(x_162);
x_163 = lean_apply_1(x_1, x_161);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
x_167 = l_Lean_Syntax_eqWithInfoAndTraceReuse(x_84, x_82, x_164);
lean_dec(x_84);
x_168 = lean_unbox(x_167);
lean_dec(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_162);
lean_free_object(x_14);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_145);
if (lean_is_scalar(x_147)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_147;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_6, 6, x_171);
x_148 = x_6;
goto block_160;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
if (lean_is_scalar(x_166)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_166;
}
lean_ctor_set(x_172, 0, x_165);
lean_ctor_set(x_172, 1, x_162);
if (lean_is_scalar(x_147)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_147;
}
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_145);
lean_ctor_set(x_14, 0, x_174);
x_148 = x_6;
goto block_160;
}
block_160:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_148, 6);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec(x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_146, 1);
lean_inc(x_152);
lean_dec(x_146);
x_153 = l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot;
x_154 = l_Lean_Language_SnapshotTask_cancelRec___rarg(x_153, x_152, x_12);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_83, x_155, x_4, x_5, x_148, x_7, x_8, x_9, x_10, x_11, x_156);
lean_dec(x_155);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_151);
lean_dec(x_146);
x_158 = lean_box(0);
x_159 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_83, x_158, x_4, x_5, x_148, x_7, x_8, x_9, x_10, x_11, x_12);
return x_159;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_175 = lean_ctor_get(x_6, 0);
x_176 = lean_ctor_get(x_6, 1);
x_177 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_178 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_179 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_180 = lean_ctor_get(x_6, 2);
x_181 = lean_ctor_get(x_6, 3);
x_182 = lean_ctor_get(x_6, 4);
x_183 = lean_ctor_get(x_6, 5);
x_184 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
x_185 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 4);
x_186 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 5);
x_187 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 6);
x_188 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 7);
x_189 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_190 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_191 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_6);
x_192 = lean_ctor_get(x_43, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_193 = x_43;
} else {
 lean_dec_ref(x_43);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_44, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_195 = x_44;
} else {
 lean_dec_ref(x_44);
 x_195 = lean_box(0);
}
x_209 = lean_ctor_get(x_194, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_194, 1);
lean_inc(x_210);
x_211 = lean_apply_1(x_1, x_209);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_215 = l_Lean_Syntax_eqWithInfoAndTraceReuse(x_84, x_82, x_212);
lean_dec(x_84);
x_216 = lean_unbox(x_215);
lean_dec(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_210);
lean_free_object(x_14);
x_217 = lean_box(0);
if (lean_is_scalar(x_193)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_193;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_192);
if (lean_is_scalar(x_195)) {
 x_219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_219 = x_195;
}
lean_ctor_set(x_219, 0, x_218);
x_220 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_220, 0, x_175);
lean_ctor_set(x_220, 1, x_176);
lean_ctor_set(x_220, 2, x_180);
lean_ctor_set(x_220, 3, x_181);
lean_ctor_set(x_220, 4, x_182);
lean_ctor_set(x_220, 5, x_183);
lean_ctor_set(x_220, 6, x_219);
lean_ctor_set_uint8(x_220, sizeof(void*)*7, x_177);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 1, x_178);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 2, x_179);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 3, x_184);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 4, x_185);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 5, x_186);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 6, x_187);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 7, x_188);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 8, x_189);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 9, x_190);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 10, x_191);
x_196 = x_220;
goto block_208;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
if (lean_is_scalar(x_214)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_214;
}
lean_ctor_set(x_221, 0, x_213);
lean_ctor_set(x_221, 1, x_210);
if (lean_is_scalar(x_195)) {
 x_222 = lean_alloc_ctor(1, 1, 0);
} else {
 x_222 = x_195;
}
lean_ctor_set(x_222, 0, x_221);
if (lean_is_scalar(x_193)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_193;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_192);
lean_ctor_set(x_14, 0, x_223);
x_224 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_224, 0, x_175);
lean_ctor_set(x_224, 1, x_176);
lean_ctor_set(x_224, 2, x_180);
lean_ctor_set(x_224, 3, x_181);
lean_ctor_set(x_224, 4, x_182);
lean_ctor_set(x_224, 5, x_183);
lean_ctor_set(x_224, 6, x_14);
lean_ctor_set_uint8(x_224, sizeof(void*)*7, x_177);
lean_ctor_set_uint8(x_224, sizeof(void*)*7 + 1, x_178);
lean_ctor_set_uint8(x_224, sizeof(void*)*7 + 2, x_179);
lean_ctor_set_uint8(x_224, sizeof(void*)*7 + 3, x_184);
lean_ctor_set_uint8(x_224, sizeof(void*)*7 + 4, x_185);
lean_ctor_set_uint8(x_224, sizeof(void*)*7 + 5, x_186);
lean_ctor_set_uint8(x_224, sizeof(void*)*7 + 6, x_187);
lean_ctor_set_uint8(x_224, sizeof(void*)*7 + 7, x_188);
lean_ctor_set_uint8(x_224, sizeof(void*)*7 + 8, x_189);
lean_ctor_set_uint8(x_224, sizeof(void*)*7 + 9, x_190);
lean_ctor_set_uint8(x_224, sizeof(void*)*7 + 10, x_191);
x_196 = x_224;
goto block_208;
}
block_208:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_196, 6);
lean_inc(x_197);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec(x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_200 = lean_ctor_get(x_194, 1);
lean_inc(x_200);
lean_dec(x_194);
x_201 = l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot;
x_202 = l_Lean_Language_SnapshotTask_cancelRec___rarg(x_201, x_200, x_12);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_83, x_203, x_4, x_5, x_196, x_7, x_8, x_9, x_10, x_11, x_204);
lean_dec(x_203);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_199);
lean_dec(x_194);
x_206 = lean_box(0);
x_207 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_83, x_206, x_4, x_5, x_196, x_7, x_8, x_9, x_10, x_11, x_12);
return x_207;
}
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_14, 0);
lean_inc(x_225);
lean_dec(x_14);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_1);
x_227 = lean_ctor_get(x_13, 1);
lean_inc(x_227);
lean_dec(x_13);
x_228 = lean_ctor_get(x_6, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_6, 1);
lean_inc(x_229);
x_230 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_231 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_232 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_233 = lean_ctor_get(x_6, 2);
lean_inc(x_233);
x_234 = lean_ctor_get(x_6, 3);
lean_inc(x_234);
x_235 = lean_ctor_get(x_6, 4);
lean_inc(x_235);
x_236 = lean_ctor_get(x_6, 5);
lean_inc(x_236);
x_237 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
x_238 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 4);
x_239 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 5);
x_240 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 6);
x_241 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 7);
x_242 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_243 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_244 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 x_245 = x_6;
} else {
 lean_dec_ref(x_6);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_225, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_247 = x_225;
} else {
 lean_dec_ref(x_225);
 x_247 = lean_box(0);
}
x_248 = lean_box(0);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_246);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_249);
if (lean_is_scalar(x_245)) {
 x_251 = lean_alloc_ctor(0, 7, 11);
} else {
 x_251 = x_245;
}
lean_ctor_set(x_251, 0, x_228);
lean_ctor_set(x_251, 1, x_229);
lean_ctor_set(x_251, 2, x_233);
lean_ctor_set(x_251, 3, x_234);
lean_ctor_set(x_251, 4, x_235);
lean_ctor_set(x_251, 5, x_236);
lean_ctor_set(x_251, 6, x_250);
lean_ctor_set_uint8(x_251, sizeof(void*)*7, x_230);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 1, x_231);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 2, x_232);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 3, x_237);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 4, x_238);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 5, x_239);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 6, x_240);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 7, x_241);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 8, x_242);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 9, x_243);
lean_ctor_set_uint8(x_251, sizeof(void*)*7 + 10, x_244);
x_252 = lean_box(0);
x_253 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_227, x_252, x_4, x_5, x_251, x_7, x_8, x_9, x_10, x_11, x_12);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; uint8_t x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_254 = lean_ctor_get(x_13, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_13, 1);
lean_inc(x_255);
lean_dec(x_13);
x_256 = lean_ctor_get(x_10, 2);
lean_inc(x_256);
x_257 = lean_ctor_get(x_6, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_6, 1);
lean_inc(x_258);
x_259 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_260 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_261 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_262 = lean_ctor_get(x_6, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_6, 3);
lean_inc(x_263);
x_264 = lean_ctor_get(x_6, 4);
lean_inc(x_264);
x_265 = lean_ctor_get(x_6, 5);
lean_inc(x_265);
x_266 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 3);
x_267 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 4);
x_268 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 5);
x_269 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 6);
x_270 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 7);
x_271 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_272 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_273 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 x_274 = x_6;
} else {
 lean_dec_ref(x_6);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_225, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_276 = x_225;
} else {
 lean_dec_ref(x_225);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_226, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_278 = x_226;
} else {
 lean_dec_ref(x_226);
 x_278 = lean_box(0);
}
x_292 = lean_ctor_get(x_277, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_277, 1);
lean_inc(x_293);
x_294 = lean_apply_1(x_1, x_292);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_297 = x_294;
} else {
 lean_dec_ref(x_294);
 x_297 = lean_box(0);
}
x_298 = l_Lean_Syntax_eqWithInfoAndTraceReuse(x_256, x_254, x_295);
lean_dec(x_256);
x_299 = lean_unbox(x_298);
lean_dec(x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_293);
x_300 = lean_box(0);
if (lean_is_scalar(x_276)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_276;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_275);
if (lean_is_scalar(x_278)) {
 x_302 = lean_alloc_ctor(1, 1, 0);
} else {
 x_302 = x_278;
}
lean_ctor_set(x_302, 0, x_301);
if (lean_is_scalar(x_274)) {
 x_303 = lean_alloc_ctor(0, 7, 11);
} else {
 x_303 = x_274;
}
lean_ctor_set(x_303, 0, x_257);
lean_ctor_set(x_303, 1, x_258);
lean_ctor_set(x_303, 2, x_262);
lean_ctor_set(x_303, 3, x_263);
lean_ctor_set(x_303, 4, x_264);
lean_ctor_set(x_303, 5, x_265);
lean_ctor_set(x_303, 6, x_302);
lean_ctor_set_uint8(x_303, sizeof(void*)*7, x_259);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 1, x_260);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 2, x_261);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 3, x_266);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 4, x_267);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 5, x_268);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 6, x_269);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 7, x_270);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 8, x_271);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 9, x_272);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 10, x_273);
x_279 = x_303;
goto block_291;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
if (lean_is_scalar(x_297)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_297;
}
lean_ctor_set(x_304, 0, x_296);
lean_ctor_set(x_304, 1, x_293);
if (lean_is_scalar(x_278)) {
 x_305 = lean_alloc_ctor(1, 1, 0);
} else {
 x_305 = x_278;
}
lean_ctor_set(x_305, 0, x_304);
if (lean_is_scalar(x_276)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_276;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_275);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
if (lean_is_scalar(x_274)) {
 x_308 = lean_alloc_ctor(0, 7, 11);
} else {
 x_308 = x_274;
}
lean_ctor_set(x_308, 0, x_257);
lean_ctor_set(x_308, 1, x_258);
lean_ctor_set(x_308, 2, x_262);
lean_ctor_set(x_308, 3, x_263);
lean_ctor_set(x_308, 4, x_264);
lean_ctor_set(x_308, 5, x_265);
lean_ctor_set(x_308, 6, x_307);
lean_ctor_set_uint8(x_308, sizeof(void*)*7, x_259);
lean_ctor_set_uint8(x_308, sizeof(void*)*7 + 1, x_260);
lean_ctor_set_uint8(x_308, sizeof(void*)*7 + 2, x_261);
lean_ctor_set_uint8(x_308, sizeof(void*)*7 + 3, x_266);
lean_ctor_set_uint8(x_308, sizeof(void*)*7 + 4, x_267);
lean_ctor_set_uint8(x_308, sizeof(void*)*7 + 5, x_268);
lean_ctor_set_uint8(x_308, sizeof(void*)*7 + 6, x_269);
lean_ctor_set_uint8(x_308, sizeof(void*)*7 + 7, x_270);
lean_ctor_set_uint8(x_308, sizeof(void*)*7 + 8, x_271);
lean_ctor_set_uint8(x_308, sizeof(void*)*7 + 9, x_272);
lean_ctor_set_uint8(x_308, sizeof(void*)*7 + 10, x_273);
x_279 = x_308;
goto block_291;
}
block_291:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 6);
lean_inc(x_280);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec(x_280);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
lean_dec(x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_283 = lean_ctor_get(x_277, 1);
lean_inc(x_283);
lean_dec(x_277);
x_284 = l_Lean_Elab_Tactic_instToSnapshotTreeTacticParsedSnapshot;
x_285 = l_Lean_Language_SnapshotTask_cancelRec___rarg(x_284, x_283, x_12);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_255, x_286, x_4, x_5, x_279, x_7, x_8, x_9, x_10, x_11, x_287);
lean_dec(x_286);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_282);
lean_dec(x_277);
x_289 = lean_box(0);
x_290 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_2, x_255, x_289, x_4, x_5, x_279, x_7, x_8, x_9, x_10, x_11, x_12);
return x_290;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lean_Syntax_getArgs(x_2);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_5 = l_Array_toSubarray___rarg(x_3, x_4, x_1);
x_6 = l_Array_ofSubarray___rarg(x_5);
lean_dec(x_5);
x_7 = lean_box(2);
x_8 = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__2;
x_9 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
x_10 = l_Lean_Syntax_getArg(x_2, x_1);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Term_runTactic___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 6);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__2___rarg(x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_10, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 6);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_10);
x_30 = lean_apply_10(x_2, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_take(x_10, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 6);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_35, 1);
lean_dec(x_40);
x_41 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
lean_ctor_set(x_35, 1, x_41);
x_42 = lean_st_ref_set(x_10, x_34, x_36);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_23);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_47);
lean_ctor_set(x_34, 6, x_50);
x_51 = lean_st_ref_set(x_10, x_34, x_36);
lean_dec(x_10);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_23);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
x_57 = lean_ctor_get(x_34, 2);
x_58 = lean_ctor_get(x_34, 3);
x_59 = lean_ctor_get(x_34, 4);
x_60 = lean_ctor_get(x_34, 5);
x_61 = lean_ctor_get(x_34, 7);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_62 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
x_63 = lean_ctor_get(x_35, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_64 = x_35;
} else {
 lean_dec_ref(x_35);
 x_64 = lean_box(0);
}
x_65 = l_Lean_PersistentArray_push___rarg(x_20, x_31);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 1);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_62);
x_67 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_67, 0, x_55);
lean_ctor_set(x_67, 1, x_56);
lean_ctor_set(x_67, 2, x_57);
lean_ctor_set(x_67, 3, x_58);
lean_ctor_set(x_67, 4, x_59);
lean_ctor_set(x_67, 5, x_60);
lean_ctor_set(x_67, 6, x_66);
lean_ctor_set(x_67, 7, x_61);
x_68 = lean_st_ref_set(x_10, x_67, x_36);
lean_dec(x_10);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_23);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_10);
x_72 = !lean_is_exclusive(x_30);
if (x_72 == 0)
{
return x_30;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_30, 0);
x_74 = lean_ctor_get(x_30, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_30);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_22, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_22, 1);
lean_inc(x_77);
lean_dec(x_22);
x_78 = lean_st_ref_get(x_10, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 6);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_inc(x_10);
x_83 = lean_apply_10(x_2, x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_80);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_take(x_10, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 6);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_87, 6);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_88, 1);
lean_dec(x_93);
x_94 = l_Lean_PersistentArray_push___rarg(x_20, x_84);
lean_ctor_set(x_88, 1, x_94);
x_95 = lean_st_ref_set(x_10, x_87, x_89);
lean_dec(x_10);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set_tag(x_95, 1);
lean_ctor_set(x_95, 0, x_76);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_76);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get_uint8(x_88, sizeof(void*)*2);
x_101 = lean_ctor_get(x_88, 0);
lean_inc(x_101);
lean_dec(x_88);
x_102 = l_Lean_PersistentArray_push___rarg(x_20, x_84);
x_103 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_100);
lean_ctor_set(x_87, 6, x_103);
x_104 = lean_st_ref_set(x_10, x_87, x_89);
lean_dec(x_10);
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
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_76);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_108 = lean_ctor_get(x_87, 0);
x_109 = lean_ctor_get(x_87, 1);
x_110 = lean_ctor_get(x_87, 2);
x_111 = lean_ctor_get(x_87, 3);
x_112 = lean_ctor_get(x_87, 4);
x_113 = lean_ctor_get(x_87, 5);
x_114 = lean_ctor_get(x_87, 7);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_87);
x_115 = lean_ctor_get_uint8(x_88, sizeof(void*)*2);
x_116 = lean_ctor_get(x_88, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_117 = x_88;
} else {
 lean_dec_ref(x_88);
 x_117 = lean_box(0);
}
x_118 = l_Lean_PersistentArray_push___rarg(x_20, x_84);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 1);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_115);
x_120 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_120, 0, x_108);
lean_ctor_set(x_120, 1, x_109);
lean_ctor_set(x_120, 2, x_110);
lean_ctor_set(x_120, 3, x_111);
lean_ctor_set(x_120, 4, x_112);
lean_ctor_set(x_120, 5, x_113);
lean_ctor_set(x_120, 6, x_119);
lean_ctor_set(x_120, 7, x_114);
x_121 = lean_st_ref_set(x_10, x_120, x_89);
lean_dec(x_10);
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
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
 lean_ctor_set_tag(x_124, 1);
}
lean_ctor_set(x_124, 0, x_76);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
uint8_t x_125; 
lean_dec(x_76);
lean_dec(x_20);
lean_dec(x_10);
x_125 = !lean_is_exclusive(x_83);
if (x_125 == 0)
{
return x_83;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_83, 0);
x_127 = lean_ctor_get(x_83, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_83);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runTactic___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_6);
x_16 = lean_array_uget(x_3, x_5);
x_17 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_MVarId_admit(x_16, x_17, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_22 = lean_box(0);
x_5 = x_21;
x_6 = x_22;
x_13 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = 0;
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Term_runTactic___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lambda__2___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lambda__1), 11, 1);
lean_closure_set(x_15, 0, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Elab_withInfoTreeContext___at_Lean_Elab_Term_runTactic___spec__21(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = l_Lean_Elab_Term_runTactic___lambda__3___closed__1;
x_20 = l_Lean_Elab_Term_withoutTacticIncrementality___at_Lean_Elab_Tactic_evalTactic_eval___spec__4(x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_15 = l_Lean_Expr_mvar___override(x_3);
x_16 = l_Lean_Meta_getMVars(x_15, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_array_size(x_17);
x_21 = 0;
x_22 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runTactic___spec__22(x_17, x_19, x_17, x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_logException___at_Lean_Elab_Term_exceptionToSorry___spec__1(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_1 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = l_Lean_Elab_Term_runTactic___lambda__4(x_1, x_2, x_3, x_14, x_4, x_5, x_6, x_7, x_11, x_12, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_11);
x_16 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError(x_8, x_9, x_4, x_5, x_6, x_7, x_11, x_12, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_runTactic___lambda__4(x_1, x_2, x_3, x_17, x_4, x_5, x_6, x_7, x_11, x_12, x_18);
lean_dec(x_17);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_runTactic___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_runTactic___lambda__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolved goals\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_runTactic___lambda__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_runTactic___lambda__6___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l_Lean_instantiateMVarDeclMVars___at_Lean_Elab_Term_runTactic___spec__1(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_30; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_14 = x_12;
} else {
 lean_dec_ref(x_12);
 x_14 = lean_box(0);
}
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Elab_Term_runTactic___lambda__6___closed__1;
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18), 12, 3);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_19);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lambda__3), 11, 2);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_20);
lean_inc(x_3);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_maybeWithoutRecovery___rarg___boxed), 11, 2);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_21);
x_70 = lean_st_ref_get(x_10, x_13);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 6);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get_uint8(x_72, sizeof(void*)*2);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_75 = l_Lean_Elab_Tactic_run(x_1, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_74);
x_30 = x_75;
goto block_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Term_withDeclName___spec__3___rarg(x_10, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_80 = l_Lean_Elab_Tactic_run(x_1, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_take(x_10, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 6);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = !lean_is_exclusive(x_84);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_84, 6);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_85, 0);
x_91 = lean_ctor_get(x_85, 1);
x_92 = lean_ctor_get(x_91, 2);
lean_inc(x_92);
x_93 = lean_nat_dec_lt(x_15, x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
lean_dec(x_92);
lean_dec(x_91);
lean_ctor_set(x_85, 1, x_78);
x_94 = lean_st_ref_set(x_10, x_84, x_86);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set(x_94, 0, x_81);
x_30 = x_94;
goto block_69;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_81);
lean_ctor_set(x_98, 1, x_97);
x_30 = x_98;
goto block_69;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_99 = lean_nat_sub(x_92, x_17);
lean_dec(x_92);
x_100 = l_Lean_Elab_instInhabitedInfoTree;
x_101 = l_Lean_PersistentArray_get_x21___rarg(x_100, x_91, x_99);
lean_dec(x_99);
lean_inc(x_1);
x_102 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_90, x_1, x_101);
lean_ctor_set(x_85, 1, x_78);
lean_ctor_set(x_85, 0, x_102);
x_103 = lean_st_ref_set(x_10, x_84, x_86);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_dec(x_105);
lean_ctor_set(x_103, 0, x_81);
x_30 = x_103;
goto block_69;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_81);
lean_ctor_set(x_107, 1, x_106);
x_30 = x_107;
goto block_69;
}
}
}
else
{
uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get_uint8(x_85, sizeof(void*)*2);
x_109 = lean_ctor_get(x_85, 0);
x_110 = lean_ctor_get(x_85, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_85);
x_111 = lean_ctor_get(x_110, 2);
lean_inc(x_111);
x_112 = lean_nat_dec_lt(x_15, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_111);
lean_dec(x_110);
x_113 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_78);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_108);
lean_ctor_set(x_84, 6, x_113);
x_114 = lean_st_ref_set(x_10, x_84, x_86);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_81);
lean_ctor_set(x_117, 1, x_115);
x_30 = x_117;
goto block_69;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = lean_nat_sub(x_111, x_17);
lean_dec(x_111);
x_119 = l_Lean_Elab_instInhabitedInfoTree;
x_120 = l_Lean_PersistentArray_get_x21___rarg(x_119, x_110, x_118);
lean_dec(x_118);
lean_inc(x_1);
x_121 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_109, x_1, x_120);
x_122 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_78);
lean_ctor_set_uint8(x_122, sizeof(void*)*2, x_108);
lean_ctor_set(x_84, 6, x_122);
x_123 = lean_st_ref_set(x_10, x_84, x_86);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_81);
lean_ctor_set(x_126, 1, x_124);
x_30 = x_126;
goto block_69;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_127 = lean_ctor_get(x_84, 0);
x_128 = lean_ctor_get(x_84, 1);
x_129 = lean_ctor_get(x_84, 2);
x_130 = lean_ctor_get(x_84, 3);
x_131 = lean_ctor_get(x_84, 4);
x_132 = lean_ctor_get(x_84, 5);
x_133 = lean_ctor_get(x_84, 7);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_84);
x_134 = lean_ctor_get_uint8(x_85, sizeof(void*)*2);
x_135 = lean_ctor_get(x_85, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_85, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_137 = x_85;
} else {
 lean_dec_ref(x_85);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_136, 2);
lean_inc(x_138);
x_139 = lean_nat_dec_lt(x_15, x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_138);
lean_dec(x_136);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(0, 2, 1);
} else {
 x_140 = x_137;
}
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_78);
lean_ctor_set_uint8(x_140, sizeof(void*)*2, x_134);
x_141 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_141, 0, x_127);
lean_ctor_set(x_141, 1, x_128);
lean_ctor_set(x_141, 2, x_129);
lean_ctor_set(x_141, 3, x_130);
lean_ctor_set(x_141, 4, x_131);
lean_ctor_set(x_141, 5, x_132);
lean_ctor_set(x_141, 6, x_140);
lean_ctor_set(x_141, 7, x_133);
x_142 = lean_st_ref_set(x_10, x_141, x_86);
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
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_81);
lean_ctor_set(x_145, 1, x_143);
x_30 = x_145;
goto block_69;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_146 = lean_nat_sub(x_138, x_17);
lean_dec(x_138);
x_147 = l_Lean_Elab_instInhabitedInfoTree;
x_148 = l_Lean_PersistentArray_get_x21___rarg(x_147, x_136, x_146);
lean_dec(x_146);
lean_inc(x_1);
x_149 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_135, x_1, x_148);
if (lean_is_scalar(x_137)) {
 x_150 = lean_alloc_ctor(0, 2, 1);
} else {
 x_150 = x_137;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_78);
lean_ctor_set_uint8(x_150, sizeof(void*)*2, x_134);
x_151 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_151, 0, x_127);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set(x_151, 2, x_129);
lean_ctor_set(x_151, 3, x_130);
lean_ctor_set(x_151, 4, x_131);
lean_ctor_set(x_151, 5, x_132);
lean_ctor_set(x_151, 6, x_150);
lean_ctor_set(x_151, 7, x_133);
x_152 = lean_st_ref_set(x_10, x_151, x_86);
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
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_81);
lean_ctor_set(x_155, 1, x_153);
x_30 = x_155;
goto block_69;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_156 = lean_ctor_get(x_80, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_80, 1);
lean_inc(x_157);
lean_dec(x_80);
x_158 = lean_st_ref_take(x_10, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_159, 6);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_162 = !lean_is_exclusive(x_159);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_159, 6);
lean_dec(x_163);
x_164 = !lean_is_exclusive(x_160);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_165 = lean_ctor_get(x_160, 0);
x_166 = lean_ctor_get(x_160, 1);
x_167 = lean_ctor_get(x_166, 2);
lean_inc(x_167);
x_168 = lean_nat_dec_lt(x_15, x_167);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
lean_dec(x_167);
lean_dec(x_166);
lean_ctor_set(x_160, 1, x_78);
x_169 = lean_st_ref_set(x_10, x_159, x_161);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_169, 0);
lean_dec(x_171);
lean_ctor_set_tag(x_169, 1);
lean_ctor_set(x_169, 0, x_156);
x_30 = x_169;
goto block_69;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_156);
lean_ctor_set(x_173, 1, x_172);
x_30 = x_173;
goto block_69;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_174 = lean_nat_sub(x_167, x_17);
lean_dec(x_167);
x_175 = l_Lean_Elab_instInhabitedInfoTree;
x_176 = l_Lean_PersistentArray_get_x21___rarg(x_175, x_166, x_174);
lean_dec(x_174);
lean_inc(x_1);
x_177 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_165, x_1, x_176);
lean_ctor_set(x_160, 1, x_78);
lean_ctor_set(x_160, 0, x_177);
x_178 = lean_st_ref_set(x_10, x_159, x_161);
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_178, 0);
lean_dec(x_180);
lean_ctor_set_tag(x_178, 1);
lean_ctor_set(x_178, 0, x_156);
x_30 = x_178;
goto block_69;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_156);
lean_ctor_set(x_182, 1, x_181);
x_30 = x_182;
goto block_69;
}
}
}
else
{
uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get_uint8(x_160, sizeof(void*)*2);
x_184 = lean_ctor_get(x_160, 0);
x_185 = lean_ctor_get(x_160, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_160);
x_186 = lean_ctor_get(x_185, 2);
lean_inc(x_186);
x_187 = lean_nat_dec_lt(x_15, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_186);
lean_dec(x_185);
x_188 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_78);
lean_ctor_set_uint8(x_188, sizeof(void*)*2, x_183);
lean_ctor_set(x_159, 6, x_188);
x_189 = lean_st_ref_set(x_10, x_159, x_161);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
 lean_ctor_set_tag(x_192, 1);
}
lean_ctor_set(x_192, 0, x_156);
lean_ctor_set(x_192, 1, x_190);
x_30 = x_192;
goto block_69;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_193 = lean_nat_sub(x_186, x_17);
lean_dec(x_186);
x_194 = l_Lean_Elab_instInhabitedInfoTree;
x_195 = l_Lean_PersistentArray_get_x21___rarg(x_194, x_185, x_193);
lean_dec(x_193);
lean_inc(x_1);
x_196 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_184, x_1, x_195);
x_197 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_78);
lean_ctor_set_uint8(x_197, sizeof(void*)*2, x_183);
lean_ctor_set(x_159, 6, x_197);
x_198 = lean_st_ref_set(x_10, x_159, x_161);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_200 = x_198;
} else {
 lean_dec_ref(x_198);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
 lean_ctor_set_tag(x_201, 1);
}
lean_ctor_set(x_201, 0, x_156);
lean_ctor_set(x_201, 1, x_199);
x_30 = x_201;
goto block_69;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_202 = lean_ctor_get(x_159, 0);
x_203 = lean_ctor_get(x_159, 1);
x_204 = lean_ctor_get(x_159, 2);
x_205 = lean_ctor_get(x_159, 3);
x_206 = lean_ctor_get(x_159, 4);
x_207 = lean_ctor_get(x_159, 5);
x_208 = lean_ctor_get(x_159, 7);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_159);
x_209 = lean_ctor_get_uint8(x_160, sizeof(void*)*2);
x_210 = lean_ctor_get(x_160, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_160, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_212 = x_160;
} else {
 lean_dec_ref(x_160);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_211, 2);
lean_inc(x_213);
x_214 = lean_nat_dec_lt(x_15, x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_213);
lean_dec(x_211);
if (lean_is_scalar(x_212)) {
 x_215 = lean_alloc_ctor(0, 2, 1);
} else {
 x_215 = x_212;
}
lean_ctor_set(x_215, 0, x_210);
lean_ctor_set(x_215, 1, x_78);
lean_ctor_set_uint8(x_215, sizeof(void*)*2, x_209);
x_216 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_216, 0, x_202);
lean_ctor_set(x_216, 1, x_203);
lean_ctor_set(x_216, 2, x_204);
lean_ctor_set(x_216, 3, x_205);
lean_ctor_set(x_216, 4, x_206);
lean_ctor_set(x_216, 5, x_207);
lean_ctor_set(x_216, 6, x_215);
lean_ctor_set(x_216, 7, x_208);
x_217 = lean_st_ref_set(x_10, x_216, x_161);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
 lean_ctor_set_tag(x_220, 1);
}
lean_ctor_set(x_220, 0, x_156);
lean_ctor_set(x_220, 1, x_218);
x_30 = x_220;
goto block_69;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_221 = lean_nat_sub(x_213, x_17);
lean_dec(x_213);
x_222 = l_Lean_Elab_instInhabitedInfoTree;
x_223 = l_Lean_PersistentArray_get_x21___rarg(x_222, x_211, x_221);
lean_dec(x_221);
lean_inc(x_1);
x_224 = l_Lean_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_210, x_1, x_223);
if (lean_is_scalar(x_212)) {
 x_225 = lean_alloc_ctor(0, 2, 1);
} else {
 x_225 = x_212;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_78);
lean_ctor_set_uint8(x_225, sizeof(void*)*2, x_209);
x_226 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_226, 0, x_202);
lean_ctor_set(x_226, 1, x_203);
lean_ctor_set(x_226, 2, x_204);
lean_ctor_set(x_226, 3, x_205);
lean_ctor_set(x_226, 4, x_206);
lean_ctor_set(x_226, 5, x_207);
lean_ctor_set(x_226, 6, x_225);
lean_ctor_set(x_226, 7, x_208);
x_227 = lean_st_ref_set(x_10, x_226, x_161);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
 lean_ctor_set_tag(x_230, 1);
}
lean_ctor_set(x_230, 0, x_156);
lean_ctor_set(x_230, 1, x_228);
x_30 = x_230;
goto block_69;
}
}
}
}
block_29:
{
uint8_t x_25; 
x_25 = l_Lean_Exception_isInterrupt(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Term_runTactic___lambda__5(x_4, x_23, x_1, x_5, x_6, x_7, x_8, x_2, x_3, x_26, x_9, x_10, x_24);
lean_dec(x_2);
lean_dec(x_6);
lean_dec(x_5);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_14)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_14;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
block_69:
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_List_isEmpty___rarg(x_32);
if (x_34 == 0)
{
lean_free_object(x_30);
if (x_4 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = l_Lean_Elab_goalsToMessageData(x_32);
x_36 = l_Lean_Elab_Term_runTactic___lambda__6___closed__3;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_5);
x_40 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_23 = x_41;
x_24 = x_42;
goto block_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_9);
lean_inc(x_3);
x_43 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_45 = l_Lean_Elab_Term_reportUnsolvedGoals(x_32, x_7, x_8, x_9, x_10, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_23 = x_46;
x_24 = x_47;
goto block_29;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
lean_ctor_set(x_30, 0, x_48);
return x_30;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_51 = l_List_isEmpty___rarg(x_49);
if (x_51 == 0)
{
if (x_4 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = l_Lean_Elab_goalsToMessageData(x_49);
x_53 = l_Lean_Elab_Term_runTactic___lambda__6___closed__3;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_5);
x_57 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_23 = x_58;
x_24 = x_59;
goto block_29;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_inc(x_9);
lean_inc(x_3);
x_60 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_62 = l_Lean_Elab_Term_reportUnsolvedGoals(x_49, x_7, x_8, x_9, x_10, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_23 = x_63;
x_24 = x_64;
goto block_29;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_49);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_50);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_30, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_30, 1);
lean_inc(x_68);
lean_dec(x_30);
x_23 = x_67;
x_24 = x_68;
goto block_29;
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_12);
if (x_231 == 0)
{
return x_12;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_12, 0);
x_233 = lean_ctor_get(x_12, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_12);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(x_4);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lambda__6___boxed), 11, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_12);
x_14 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_15);
if (x_16 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_17; 
lean_free_object(x_11);
x_17 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseContraints(x_3, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_4);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = 1;
x_20 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_1, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_processPostponedUniverseContraints(x_3, x_4, x_5, x_6, x_7, x_8, x_18);
lean_dec(x_4);
return x_22;
}
}
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
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__8(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__10(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__11(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__12(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__13(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__15(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__16(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_Lean_Elab_Term_runTactic___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__17(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_Lean_Elab_Term_runTactic___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentArray_foldlM___at_Lean_Elab_Term_runTactic___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Term_runTactic___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_LocalContext_foldlM___at_Lean_Elab_Term_runTactic___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_withNarrowedTacticReuse___at_Lean_Elab_Term_runTactic___spec__19___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runTactic___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runTactic___spec__22(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_runTactic___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Elab_Term_runTactic___lambda__4(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l_Lean_Elab_Term_runTactic___lambda__5(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Elab_Term_runTactic___lambda__6(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Elab_Term_runTactic(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = 0;
x_19 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_18, x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_7 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_st_ref_get(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_4, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_52; lean_object* x_53; lean_object* x_79; 
x_18 = lean_ctor_get(x_15, 2);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_15, 2, x_19);
x_20 = lean_st_ref_set(x_4, x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_79 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_83 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_2, x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = 0;
x_86 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_2, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_box(0);
x_88 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_80, x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_84);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_22 = x_89;
x_23 = x_90;
goto block_51;
}
else
{
lean_object* x_91; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(x_3, x_4, x_5, x_6, x_7, x_8, x_84);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_80, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_93);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_92);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_22 = x_95;
x_23 = x_96;
goto block_51;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_97 = lean_ctor_get(x_91, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_52 = x_97;
x_53 = x_98;
goto block_78;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_80);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_99 = lean_ctor_get(x_83, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_83, 1);
lean_inc(x_100);
lean_dec(x_83);
x_52 = x_99;
x_53 = x_100;
goto block_78;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_101 = lean_ctor_get(x_79, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_79, 1);
lean_inc(x_102);
lean_dec(x_79);
x_52 = x_101;
x_53 = x_102;
goto block_78;
}
block_51:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_st_ref_take(x_4, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_25, 2);
x_29 = l_List_appendTR___rarg(x_28, x_13);
lean_ctor_set(x_25, 2, x_29);
x_30 = lean_st_ref_set(x_4, x_25, x_26);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
lean_dec(x_22);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
x_39 = lean_ctor_get(x_25, 2);
x_40 = lean_ctor_get(x_25, 3);
x_41 = lean_ctor_get(x_25, 4);
x_42 = lean_ctor_get(x_25, 5);
x_43 = lean_ctor_get(x_25, 6);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_44 = l_List_appendTR___rarg(x_39, x_13);
x_45 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 4, x_41);
lean_ctor_set(x_45, 5, x_42);
lean_ctor_set(x_45, 6, x_43);
x_46 = lean_st_ref_set(x_4, x_45, x_26);
lean_dec(x_4);
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
x_49 = lean_ctor_get(x_22, 0);
lean_inc(x_49);
lean_dec(x_22);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
block_78:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_st_ref_take(x_4, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_55, 2);
x_59 = l_List_appendTR___rarg(x_58, x_13);
lean_ctor_set(x_55, 2, x_59);
x_60 = lean_st_ref_set(x_4, x_55, x_56);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_52);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_65 = lean_ctor_get(x_55, 0);
x_66 = lean_ctor_get(x_55, 1);
x_67 = lean_ctor_get(x_55, 2);
x_68 = lean_ctor_get(x_55, 3);
x_69 = lean_ctor_get(x_55, 4);
x_70 = lean_ctor_get(x_55, 5);
x_71 = lean_ctor_get(x_55, 6);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_55);
x_72 = l_List_appendTR___rarg(x_67, x_13);
x_73 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_73, 0, x_65);
lean_ctor_set(x_73, 1, x_66);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_68);
lean_ctor_set(x_73, 4, x_69);
lean_ctor_set(x_73, 5, x_70);
lean_ctor_set(x_73, 6, x_71);
x_74 = lean_st_ref_set(x_4, x_73, x_56);
lean_dec(x_4);
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
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
 lean_ctor_set_tag(x_77, 1);
}
lean_ctor_set(x_77, 0, x_52);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_134; lean_object* x_135; lean_object* x_154; 
x_103 = lean_ctor_get(x_15, 0);
x_104 = lean_ctor_get(x_15, 1);
x_105 = lean_ctor_get(x_15, 3);
x_106 = lean_ctor_get(x_15, 4);
x_107 = lean_ctor_get(x_15, 5);
x_108 = lean_ctor_get(x_15, 6);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_15);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_110, 0, x_103);
lean_ctor_set(x_110, 1, x_104);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_110, 3, x_105);
lean_ctor_set(x_110, 4, x_106);
lean_ctor_set(x_110, 5, x_107);
lean_ctor_set(x_110, 6, x_108);
x_111 = lean_st_ref_set(x_4, x_110, x_16);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_154 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_112);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_158 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_2, x_157, x_3, x_4, x_5, x_6, x_7, x_8, x_156);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; uint8_t x_160; uint8_t x_161; 
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_160 = 0;
x_161 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_beqPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4274_(x_2, x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_box(0);
x_163 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_155, x_162, x_3, x_4, x_5, x_6, x_7, x_8, x_159);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_113 = x_164;
x_114 = x_165;
goto block_133;
}
else
{
lean_object* x_166; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_166 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultLoop(x_3, x_4, x_5, x_6, x_7, x_8, x_159);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_155, x_167, x_3, x_4, x_5, x_6, x_7, x_8, x_168);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_167);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_113 = x_170;
x_114 = x_171;
goto block_133;
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_155);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_172 = lean_ctor_get(x_166, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_166, 1);
lean_inc(x_173);
lean_dec(x_166);
x_134 = x_172;
x_135 = x_173;
goto block_153;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_155);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_174 = lean_ctor_get(x_158, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_158, 1);
lean_inc(x_175);
lean_dec(x_158);
x_134 = x_174;
x_135 = x_175;
goto block_153;
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_176 = lean_ctor_get(x_154, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_154, 1);
lean_inc(x_177);
lean_dec(x_154);
x_134 = x_176;
x_135 = x_177;
goto block_153;
}
block_133:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_115 = lean_st_ref_take(x_4, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_116, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_116, 5);
lean_inc(x_123);
x_124 = lean_ctor_get(x_116, 6);
lean_inc(x_124);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 lean_ctor_release(x_116, 4);
 lean_ctor_release(x_116, 5);
 lean_ctor_release(x_116, 6);
 x_125 = x_116;
} else {
 lean_dec_ref(x_116);
 x_125 = lean_box(0);
}
x_126 = l_List_appendTR___rarg(x_120, x_13);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 7, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_118);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_121);
lean_ctor_set(x_127, 4, x_122);
lean_ctor_set(x_127, 5, x_123);
lean_ctor_set(x_127, 6, x_124);
x_128 = lean_st_ref_set(x_4, x_127, x_117);
lean_dec(x_4);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_113, 0);
lean_inc(x_131);
lean_dec(x_113);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
block_153:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_136 = lean_st_ref_take(x_4, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_137, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 5);
lean_inc(x_144);
x_145 = lean_ctor_get(x_137, 6);
lean_inc(x_145);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 lean_ctor_release(x_137, 3);
 lean_ctor_release(x_137, 4);
 lean_ctor_release(x_137, 5);
 lean_ctor_release(x_137, 6);
 x_146 = x_137;
} else {
 lean_dec_ref(x_137);
 x_146 = lean_box(0);
}
x_147 = l_List_appendTR___rarg(x_141, x_13);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 7, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_139);
lean_ctor_set(x_148, 1, x_140);
lean_ctor_set(x_148, 2, x_147);
lean_ctor_set(x_148, 3, x_142);
lean_ctor_set(x_148, 4, x_143);
lean_ctor_set(x_148, 5, x_144);
lean_ctor_set(x_148, 6, x_145);
x_149 = lean_st_ref_set(x_4, x_148, x_138);
lean_dec(x_4);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
 lean_ctor_set_tag(x_152, 1);
}
lean_ctor_set(x_152, 0, x_134);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesize___rarg___lambda__1___boxed), 10, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_apply_3(x_1, lean_box(0), x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesize___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_withSynthesize___rarg___lambda__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesize___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Elab_Term_withSynthesize___rarg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_3, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_48; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 2, x_18);
x_19 = lean_st_ref_set(x_3, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_48 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = 0;
x_52 = 0;
lean_inc(x_3);
x_53 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_51, x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_take(x_3, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_56, 2);
x_60 = l_List_appendTR___rarg(x_59, x_12);
lean_ctor_set(x_56, 2, x_60);
x_61 = lean_st_ref_set(x_3, x_56, x_57);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_49);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_66 = lean_ctor_get(x_56, 0);
x_67 = lean_ctor_get(x_56, 1);
x_68 = lean_ctor_get(x_56, 2);
x_69 = lean_ctor_get(x_56, 3);
x_70 = lean_ctor_get(x_56, 4);
x_71 = lean_ctor_get(x_56, 5);
x_72 = lean_ctor_get(x_56, 6);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_56);
x_73 = l_List_appendTR___rarg(x_68, x_12);
x_74 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_67);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_69);
lean_ctor_set(x_74, 4, x_70);
lean_ctor_set(x_74, 5, x_71);
lean_ctor_set(x_74, 6, x_72);
x_75 = lean_st_ref_set(x_3, x_74, x_57);
lean_dec(x_3);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_49);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_49);
x_79 = lean_ctor_get(x_53, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_53, 1);
lean_inc(x_80);
lean_dec(x_53);
x_21 = x_79;
x_22 = x_80;
goto block_47;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_81 = lean_ctor_get(x_48, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 1);
lean_inc(x_82);
lean_dec(x_48);
x_21 = x_81;
x_22 = x_82;
goto block_47;
}
block_47:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_st_ref_take(x_3, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 2);
x_28 = l_List_appendTR___rarg(x_27, x_12);
lean_ctor_set(x_24, 2, x_28);
x_29 = lean_st_ref_set(x_3, x_24, x_25);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_21);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
x_36 = lean_ctor_get(x_24, 2);
x_37 = lean_ctor_get(x_24, 3);
x_38 = lean_ctor_get(x_24, 4);
x_39 = lean_ctor_get(x_24, 5);
x_40 = lean_ctor_get(x_24, 6);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
x_41 = l_List_appendTR___rarg(x_36, x_12);
x_42 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 4, x_38);
lean_ctor_set(x_42, 5, x_39);
lean_ctor_set(x_42, 6, x_40);
x_43 = lean_st_ref_set(x_3, x_42, x_25);
lean_dec(x_3);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_21);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_113; 
x_83 = lean_ctor_get(x_14, 0);
x_84 = lean_ctor_get(x_14, 1);
x_85 = lean_ctor_get(x_14, 3);
x_86 = lean_ctor_get(x_14, 4);
x_87 = lean_ctor_get(x_14, 5);
x_88 = lean_ctor_get(x_14, 6);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_14);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_84);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_85);
lean_ctor_set(x_90, 4, x_86);
lean_ctor_set(x_90, 5, x_87);
lean_ctor_set(x_90, 6, x_88);
x_91 = lean_st_ref_set(x_3, x_90, x_15);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_113 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_92);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = 0;
x_117 = 0;
lean_inc(x_3);
x_118 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_116, x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_115);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_st_ref_take(x_3, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_121, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_121, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_121, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_121, 5);
lean_inc(x_128);
x_129 = lean_ctor_get(x_121, 6);
lean_inc(x_129);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 lean_ctor_release(x_121, 4);
 lean_ctor_release(x_121, 5);
 lean_ctor_release(x_121, 6);
 x_130 = x_121;
} else {
 lean_dec_ref(x_121);
 x_130 = lean_box(0);
}
x_131 = l_List_appendTR___rarg(x_125, x_12);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 7, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_123);
lean_ctor_set(x_132, 1, x_124);
lean_ctor_set(x_132, 2, x_131);
lean_ctor_set(x_132, 3, x_126);
lean_ctor_set(x_132, 4, x_127);
lean_ctor_set(x_132, 5, x_128);
lean_ctor_set(x_132, 6, x_129);
x_133 = lean_st_ref_set(x_3, x_132, x_122);
lean_dec(x_3);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_114);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_114);
x_137 = lean_ctor_get(x_118, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_118, 1);
lean_inc(x_138);
lean_dec(x_118);
x_93 = x_137;
x_94 = x_138;
goto block_112;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_139 = lean_ctor_get(x_113, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_113, 1);
lean_inc(x_140);
lean_dec(x_113);
x_93 = x_139;
x_94 = x_140;
goto block_112;
}
block_112:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_95 = lean_st_ref_take(x_3, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_96, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_96, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 lean_ctor_release(x_96, 5);
 lean_ctor_release(x_96, 6);
 x_105 = x_96;
} else {
 lean_dec_ref(x_96);
 x_105 = lean_box(0);
}
x_106 = l_List_appendTR___rarg(x_100, x_12);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 7, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_98);
lean_ctor_set(x_107, 1, x_99);
lean_ctor_set(x_107, 2, x_106);
lean_ctor_set(x_107, 3, x_101);
lean_ctor_set(x_107, 4, x_102);
lean_ctor_set(x_107, 5, x_103);
lean_ctor_set(x_107, 6, x_104);
x_108 = lean_st_ref_set(x_3, x_107, x_97);
lean_dec(x_3);
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
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
 lean_ctor_set_tag(x_111, 1);
}
lean_ctor_set(x_111, 0, x_93);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeLightImp___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesizeLight___rarg___lambda__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1;
x_4 = lean_apply_3(x_1, lean_box(0), x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withSynthesizeLight(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesizeLight___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_box(x_10);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_7, 5);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
lean_ctor_set(x_7, 5, x_16);
x_17 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_13, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
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
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
x_28 = lean_ctor_get(x_7, 2);
x_29 = lean_ctor_get(x_7, 3);
x_30 = lean_ctor_get(x_7, 4);
x_31 = lean_ctor_get(x_7, 5);
x_32 = lean_ctor_get(x_7, 6);
x_33 = lean_ctor_get(x_7, 7);
x_34 = lean_ctor_get(x_7, 8);
x_35 = lean_ctor_get(x_7, 9);
x_36 = lean_ctor_get(x_7, 10);
x_37 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_38 = lean_ctor_get(x_7, 11);
x_39 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_40 = l_Lean_replaceRef(x_1, x_31);
lean_dec(x_31);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_27);
lean_ctor_set(x_41, 2, x_28);
lean_ctor_set(x_41, 3, x_29);
lean_ctor_set(x_41, 4, x_30);
lean_ctor_set(x_41, 5, x_40);
lean_ctor_set(x_41, 6, x_32);
lean_ctor_set(x_41, 7, x_33);
lean_ctor_set(x_41, 8, x_34);
lean_ctor_set(x_41, 9, x_35);
lean_ctor_set(x_41, 10, x_36);
lean_ctor_set(x_41, 11, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*12, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*12 + 1, x_39);
x_42 = 1;
lean_inc(x_8);
lean_inc(x_41);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_43 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_13, x_42, x_3, x_4, x_5, x_6, x_41, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_44, x_3, x_4, x_5, x_6, x_41, x_8, x_45);
lean_dec(x_8);
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_41);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_49 = x_43;
} else {
 lean_dec_ref(x_43);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l_Lean_Elab_Term_runTactic(x_1, x_2, x_3, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_markAsResolved(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
x_16 = lean_array_uget(x_3, x_5);
x_24 = l_Lean_getDelayedMVarRoot___at_Lean_Elab_Term_isLetRecAuxMVar___spec__1(x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getSyntheticMVarDecl_x3f(x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1;
x_17 = x_30;
x_18 = x_29;
goto block_23;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 2)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___lambda__1), 10, 3);
lean_closure_set(x_37, 0, x_25);
lean_closure_set(x_37, 1, x_34);
lean_closure_set(x_37, 2, x_36);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Elab_Term_withSavedContext___rarg(x_35, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1;
x_17 = x_40;
x_18 = x_39;
goto block_23;
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_32);
lean_dec(x_25);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec(x_27);
x_46 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1;
x_17 = x_46;
x_18 = x_45;
goto block_23;
}
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_19;
x_13 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_runPendingTacticsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_Meta_getMVars(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_array_size(x_10);
x_14 = 0;
x_15 = lean_box(0);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1(x_10, x_12, x_10, x_13, x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resume", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__4;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__5;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__7;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__9;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__11;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__12;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SyntheticMVars", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__13;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__15;
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__17;
x_2 = lean_unsigned_to_nat(7115u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__2;
x_3 = 0;
x_4 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__18;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_NumObjs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_OccursCheck(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_NumObjs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_OccursCheck(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1 = _init_l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1();
lean_mark_persistent(l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__1);
l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__2 = _init_l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__2();
lean_mark_persistent(l_Lean_occursCheck_visitMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__3___closed__2);
l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__1 = _init_l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__1();
lean_mark_persistent(l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__1);
l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__2 = _init_l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__2();
lean_mark_persistent(l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__2);
l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__3 = _init_l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__3();
lean_mark_persistent(l_Lean_occursCheck___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__2___closed__3);
l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1___closed__1 = _init_l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___spec__1___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__4);
l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1 = _init_l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_getDefaultInstancesPriorities___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__1___rarg___closed__1);
l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__1 = _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__1();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__1);
l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2 = _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__2);
l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__3 = _init_l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__3();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___spec__2___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefault___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__5 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__5);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__6);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__7 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__7);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__2___closed__8);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeUsingDefaultPrio_synthesizeUsingDefaultInstance___lambda__3___closed__5);
l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__1 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__1);
l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__1___closed__2);
l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__1 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__1);
l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__2 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___lambda__2___closed__2);
l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__1);
l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2 = _init_l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportStuckSyntheticMVar___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSyntheticMVarsRef___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___spec__11___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_throwStuckAtUniverseCnstr___closed__4);
l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___closed__1 = _init_l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_PostponeBehavior_noConfusion___rarg___closed__1);
l_Lean_Elab_Term_instInhabitedPostponeBehavior = _init_l_Lean_Elab_Term_instInhabitedPostponeBehavior();
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__5 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__5();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__5);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__6 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__6();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__6);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__7 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__7();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__7);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__8 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__8();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__8);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__9 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__9();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__9);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__10 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__10();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__10);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__11 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__11();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__11);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__12 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__12();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__12);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__13 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__13();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__13);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__14 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__14();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__14);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__15 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__15();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__15);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__16 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__16();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__16);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__17 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__17();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__17);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__18 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__18();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__18);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__19 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__19();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__19);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__20 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__20();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reprPostponeBehavior____x40_Lean_Elab_SyntheticMVars___hyg_4158____closed__20);
l_Lean_Elab_Term_instReprPostponeBehavior___closed__1 = _init_l_Lean_Elab_Term_instReprPostponeBehavior___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_instReprPostponeBehavior___closed__1);
l_Lean_Elab_Term_instReprPostponeBehavior = _init_l_Lean_Elab_Term_instReprPostponeBehavior();
lean_mark_persistent(l_Lean_Elab_Term_instReprPostponeBehavior);
l_Lean_Elab_Term_instBEqPostponeBehavior___closed__1 = _init_l_Lean_Elab_Term_instBEqPostponeBehavior___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_instBEqPostponeBehavior___closed__1);
l_Lean_Elab_Term_instBEqPostponeBehavior = _init_l_Lean_Elab_Term_instBEqPostponeBehavior();
lean_mark_persistent(l_Lean_Elab_Term_instBEqPostponeBehavior);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__5 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__5();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__5);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__6 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__6();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__6);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__7 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__7();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__7);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__8 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__8();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_TacticMVarKind_logError___closed__8);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_synthesizeSyntheticMVars_loop___spec__1___closed__6);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__1 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__1);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__2 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__2);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__3 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__3();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__3);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__4 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__4();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__4);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__5 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__5();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__5);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__6 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__6();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__2___closed__6);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__5 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__5);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__6 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__6);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__7 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__7);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__8 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__8();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__8);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__9 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__9();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__9);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__10 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__10();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__10);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__11 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__11();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__11);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__12 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__12();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__12);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__13 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__13();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__13);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__14 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__14();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__14);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__15 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__15();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__15);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__16 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__16();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__16);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__17 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__17();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__17);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__18 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__18();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__18);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__19 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__19();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__19);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__20 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__20();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__20);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__21 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__21();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__21);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__22 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__22();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___lambda__1___closed__22);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___lambda__2___closed__1();
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___closed__1);
l_panic___at_Lean_Elab_Term_runTactic___spec__3___closed__1 = _init_l_panic___at_Lean_Elab_Term_runTactic___spec__3___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_runTactic___spec__3___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__4);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_runTactic___spec__9___closed__5);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6___closed__1 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6___closed__1();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at_Lean_Elab_Term_runTactic___spec__6___closed__1);
l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__1 = _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__1();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__1);
l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__2 = _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__2();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__2);
l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__3 = _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__3();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__3);
l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__4 = _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__4();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__4);
l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__5 = _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__5();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__5);
l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__6 = _init_l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__6();
lean_mark_persistent(l_Lean_instantiateLCtxMVars___at_Lean_Elab_Term_runTactic___spec__2___closed__6);
l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__1 = _init_l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__1);
l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__2 = _init_l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_withNarrowedArgTacticReuse___at_Lean_Elab_Term_runTactic___spec__18___lambda__1___closed__2);
l_Lean_Elab_Term_runTactic___lambda__3___closed__1 = _init_l_Lean_Elab_Term_runTactic___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_runTactic___lambda__3___closed__1);
l_Lean_Elab_Term_runTactic___lambda__6___closed__1 = _init_l_Lean_Elab_Term_runTactic___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_runTactic___lambda__6___closed__1);
l_Lean_Elab_Term_runTactic___lambda__6___closed__2 = _init_l_Lean_Elab_Term_runTactic___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_runTactic___lambda__6___closed__2);
l_Lean_Elab_Term_runTactic___lambda__6___closed__3 = _init_l_Lean_Elab_Term_runTactic___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_runTactic___lambda__6___closed__3);
l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1 = _init_l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withSynthesizeLight___rarg___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Term_runPendingTacticsAt___spec__1___closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__1 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__2 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__2);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__3 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__3);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__4 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__4();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__4);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__5 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__5();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__5);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__6 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__6();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__6);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__7 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__7();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__7);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__8 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__8();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__8);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__9 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__9();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__9);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__10 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__10();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__10);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__11 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__11();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__11);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__12 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__12();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__12);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__13 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__13();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__13);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__14 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__14();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__14);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__15 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__15();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__15);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__16 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__16();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__16);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__17 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__17();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__17);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__18 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__18();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115____closed__18);
if (builtin) {res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_SyntheticMVars___hyg_7115_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
